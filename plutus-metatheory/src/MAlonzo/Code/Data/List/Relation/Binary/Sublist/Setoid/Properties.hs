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

module MAlonzo.Code.Data.List.Relation.Binary.Sublist.Setoid.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous
import qualified MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core
import qualified MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
import qualified MAlonzo.Code.Data.List.Relation.Binary.Sublist.Setoid
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Maybe.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Properties.Setoid
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Double
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.trans
d_trans_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_26 ~v0 ~v1 v2 = du_trans_26 v2
du_trans_26 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_26 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._._≋_
d__'8779'__32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8779'__32 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._._⊆_
d__'8838'__76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8838'__76 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.Disjoint
d_Disjoint_84 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.fromAny
d_fromAny_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_fromAny_98 ~v0 ~v1 ~v2 = du_fromAny_98
du_fromAny_98 ::
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_fromAny_98 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.du_fromAny_74
      v1 v2
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.toAny
d_toAny_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_toAny_104 ~v0 ~v1 ~v2 = du_toAny_104
du_toAny_104 ::
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_toAny_104 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.du_toAny_60
      v2 v3
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.refl
d_refl_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_refl_126 ~v0 ~v1 v2 = du_refl_126 v2
du_refl_126 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_refl_126 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_refl_1116
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.trans
d_trans_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_trans_130 ~v0 ~v1 v2 = du_trans_130 v2
du_trans_130 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_trans_130 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_trans_1140
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.Sublist
d_Sublist_189 a0 a1 a2 a3 a4 = ()
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.∷-injectiveˡ
d_'8759''45'injective'737'_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8759''45'injective'737'_230 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.∷-injectiveʳ
d_'8759''45'injective'691'_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8759''45'injective'691'_240 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.∷ʳ-injective
d_'8759''691''45'injective_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8759''691''45'injective_246 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.⊆-trans-idˡ
d_'8838''45'trans'45'id'737'_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8838''45'trans'45'id'737'_262 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.⊆-trans-idʳ
d_'8838''45'trans'45'id'691'_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8838''45'trans'45'id'691'_288 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.⊆-trans-assoc
d_'8838''45'trans'45'assoc_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8838''45'trans'45'assoc_326 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning._IsRelatedTo_
d__IsRelatedTo__366 a0 a1 a2 a3 a4 = ()
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning._∎
d__'8718'_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d__'8718'_368 ~v0 ~v1 v2 = du__'8718'_368 v2
du__'8718'_368 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du__'8718'_368 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                  (coe v3)))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.IsEquality
d_IsEquality_370 a0 a1 a2 a3 a4 a5 = ()
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.IsEquality?
d_IsEquality'63'_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsEquality'63'_372 ~v0 ~v1 ~v2 = du_IsEquality'63'_372
du_IsEquality'63'_372 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_IsEquality'63'_372 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_IsEquality'63'_138
      v2
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.begin_
d_begin__374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_begin__374 ~v0 ~v1 v2 = du_begin__374 v2
du_begin__374 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_begin__374 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
                  (coe v3)))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.begin_
d_begin__376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_begin__376 ~v0 ~v1 ~v2 = du_begin__376
du_begin__376 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_begin__376
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
           (coe v0) v1 v2 v3)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.equalitySubRelation
d_equalitySubRelation_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_equalitySubRelation_378 ~v0 ~v1 ~v2 = du_equalitySubRelation_378
du_equalitySubRelation_378 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
du_equalitySubRelation_378
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.extractEquality
d_extractEquality_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T_IsEquality_122 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_extractEquality_382 ~v0 ~v1 ~v2 = du_extractEquality_382
du_extractEquality_382 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T_IsEquality_122 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_extractEquality_382 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_extractEquality_148
      v2 v3
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.start
d_start_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_start_388 ~v0 ~v1 v2 = du_start_388 v2
du_start_388 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_start_388 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v2))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-∼
d_step'45''8764'_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8764'_390 ~v0 ~v1 v2 = du_step'45''8764'_390 v2
du_step'45''8764'_390 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8764'_390 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_300
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                  (coe v3)))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-≈
d_step'45''8776'_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8776'_392 ~v0 ~v1 v2 = du_step'45''8776'_392 v2
du_step'45''8776'_392 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8776'_392 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776'_372
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                  (coe v3)))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-≈-⟨
d_step'45''8776''45''10216'_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8776''45''10216'_394 ~v0 ~v1 v2
  = du_step'45''8776''45''10216'_394 v2
du_step'45''8776''45''10216'_394 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8776''45''10216'_394 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                  (coe v3))
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                     (coe v3))))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-≈-⟩
d_step'45''8776''45''10217'_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8776''45''10217'_396 ~v0 ~v1 v2
  = du_step'45''8776''45''10217'_396 v2
du_step'45''8776''45''10217'_396 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8776''45''10217'_396 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                  (coe v3)))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-≈˘
d_step'45''8776''728'_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8776''728'_398 ~v0 ~v1 v2
  = du_step'45''8776''728'_398 v2
du_step'45''8776''728'_398 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8776''728'_398 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''728'_374
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                  (coe v3))
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                     (coe v3))))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-≋
d_step'45''8779'_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8779'_400 ~v0 ~v1 v2 = du_step'45''8779'_400 v2
du_step'45''8779'_400 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8779'_400 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8779'_382
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
            (coe
               MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_isPreorder_1316
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v1)))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-≋-⟨
d_step'45''8779''45''10216'_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8779''45''10216'_402 ~v0 ~v1 v2
  = du_step'45''8779''45''10216'_402 v2
du_step'45''8779''45''10216'_402 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8779''45''10216'_402 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8779''45''10216'_380
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
            (coe
               MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_isPreorder_1316
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v1))))
         (coe
            MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_symmetric_40
            (let v2
                   = coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_setoid_184 (coe v1) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v2))))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-≋-⟩
d_step'45''8779''45''10217'_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8779''45''10217'_404 ~v0 ~v1 v2
  = du_step'45''8779''45''10217'_404 v2
du_step'45''8779''45''10217'_404 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8779''45''10217'_404 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8779''45''10217'_378
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
            (coe
               MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_isPreorder_1316
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v1)))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-≋˘
d_step'45''8779''728'_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8779''728'_406 ~v0 ~v1 v2
  = du_step'45''8779''728'_406 v2
du_step'45''8779''728'_406 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8779''728'_406 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8779''728'_384
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
            (coe
               MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_isPreorder_1316
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v1))))
         (coe
            MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_symmetric_40
            (let v2
                   = coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_setoid_184 (coe v1) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v2))))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-≡
d_step'45''8801'_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801'_408 ~v0 ~v1 ~v2 = du_step'45''8801'_408
du_step'45''8801'_408 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8801'_408
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-≡-∣
d_step'45''8801''45''8739'_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801''45''8739'_410 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_step'45''8801''45''8739'_410 v5
du_step'45''8801''45''8739'_410 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8801''45''8739'_410 v0 = coe v0
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-≡-⟨
d_step'45''8801''45''10216'_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801''45''10216'_412 ~v0 ~v1 ~v2
  = du_step'45''8801''45''10216'_412
du_step'45''8801''45''10216'_412 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8801''45''10216'_412
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-≡-⟩
d_step'45''8801''45''10217'_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801''45''10217'_414 ~v0 ~v1 ~v2
  = du_step'45''8801''45''10217'_414
du_step'45''8801''45''10217'_414 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8801''45''10217'_414
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-≡˘
d_step'45''8801''728'_416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8801''728'_416 ~v0 ~v1 ~v2 = du_step'45''8801''728'_416
du_step'45''8801''728'_416 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8801''728'_416
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-≲
d_step'45''8818'_418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8818'_418 ~v0 ~v1 v2 = du_step'45''8818'_418 v2
du_step'45''8818'_418 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8818'_418 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8818'_304
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                  (coe v3)))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.step-⊆
d_step'45''8838'_420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_step'45''8838'_420 ~v0 ~v1 v2 = du_step'45''8838'_420 v2
du_step'45''8838'_420 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_step'45''8838'_420 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8838'_316
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
            (coe
               MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_isPreorder_1316
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v1)))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.stop
d_stop_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_stop_422 ~v0 ~v1 v2 = du_stop_422 v2
du_stop_422 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_stop_422 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v2))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.≈-go
d_'8776''45'go_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_'8776''45'go_424 ~v0 ~v1 v2 = du_'8776''45'go_424 v2
du_'8776''45'go_424 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_'8776''45'go_424 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v2))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.≡-go
d_'8801''45'go_426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_'8801''45'go_426 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8801''45'go_426 v7
du_'8801''45'go_426 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_'8801''45'go_426 v0 = coe v0
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.⊆-Reasoning.≲-go
d_'8818''45'go_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
d_'8818''45'go_428 ~v0 ~v1 v2 = du_'8818''45'go_428 v2
du_'8818''45'go_428 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.T__IsRelatedTo__62
du_'8818''45'go_428 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v2))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.tail-⊆
d_tail'45''8838'_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> MAlonzo.Code.Data.Maybe.Relation.Unary.All.T_All_18
d_tail'45''8838'_444 ~v0 ~v1 v2 v3 = du_tail'45''8838'_444 v2 v3
du_tail'45''8838'_444 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> MAlonzo.Code.Data.Maybe.Relation.Unary.All.T_All_18
du_tail'45''8838'_444 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_tail'45'Sublist_168
      (coe v1) (coe v1)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_refl_1116
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
         (coe v1))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.take-⊆
d_take'45''8838'_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  Integer ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_take'45''8838'_452 ~v0 ~v1 v2 v3 v4
  = du_take'45''8838'_452 v2 v3 v4
du_take'45''8838'_452 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  Integer ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_take'45''8838'_452 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_take'45'Sublist_182
      (coe v2) (coe v2) (coe v1)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_refl_1116
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
         (coe v2))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.drop-⊆
d_drop'45''8838'_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  Integer ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_drop'45''8838'_462 ~v0 ~v1 v2 v3 v4
  = du_drop'45''8838'_462 v2 v3 v4
du_drop'45''8838'_462 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  Integer ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_drop'45''8838'_462 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_drop'45'Sublist_202
      (coe v1) (coe v2) (coe v2)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_refl_1116
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
         (coe v2))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.takeWhile-⊆
d_takeWhile'45''8838'_478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_takeWhile'45''8838'_478 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_takeWhile'45''8838'_478 v2 v5 v6
du_takeWhile'45''8838'_478 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_takeWhile'45''8838'_478 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_takeWhile'45'Sublist_238
      (coe v1) (coe v2) (coe v2)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_refl_1116
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
         (coe v2))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.dropWhile-⊆
d_dropWhile'45''8838'_484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_dropWhile'45''8838'_484 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_dropWhile'45''8838'_484 v2 v5 v6
du_dropWhile'45''8838'_484 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_dropWhile'45''8838'_484 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_dropWhile'45'Sublist_272
      (coe v1) (coe v2) (coe v2)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_refl_1116
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
         (coe v2))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.filter-⊆
d_filter'45''8838'_490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_filter'45''8838'_490 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_filter'45''8838'_490 v2 v5 v6
du_filter'45''8838'_490 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_filter'45''8838'_490 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_filter'45'Sublist_306
      (coe v1) (coe v2) (coe v2)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_refl_1116
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
         (coe v2))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.takeWhile⊆filter
d_takeWhile'8838'filter_504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_takeWhile'8838'filter_504 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_takeWhile'8838'filter_504 v2 v5 v6
du_takeWhile'8838'filter_504 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_takeWhile'8838'filter_504 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_takeWhile'45'filter_906
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
            (coe
               MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
               (coe v0)))
         v2)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.filter⊆dropWhile
d_filter'8838'dropWhile_510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_filter'8838'dropWhile_510 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_filter'8838'dropWhile_510 v2 v5 v6
du_filter'8838'dropWhile_510 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_filter'8838'dropWhile_510 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_filter'45'dropWhile_936
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
            (coe
               MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
               (coe v0)))
         v2)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.∷ˡ⁻
d_'8759''737''8315'_518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_'8759''737''8315'_518 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8759''737''8315'_518 v5
du_'8759''737''8315'_518 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_'8759''737''8315'_518 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_'8759''737''8315'_352
      (coe v0)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.∷ʳ⁻
d_'8759''691''8315'_520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_'8759''691''8315'_520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8759''691''8315'_520
du_'8759''691''8315'_520 ::
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_'8759''691''8315'_520 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_'8759''691''8315'_362
      v1
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.∷⁻
d_'8759''8315'_522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_'8759''8315'_522 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8759''8315'_522 v6
du_'8759''8315'_522 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_'8759''8315'_522 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_'8759''8315'_376
      (coe v0)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._._._⊆_
d__'8838'__542 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8838'__542 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.map⁺
d_map'8314'_550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_map'8314'_550 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 v9 v10
  = du_map'8314'_550 v6 v7 v9 v10
du_map'8314'_550 ::
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_map'8314'_550 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_map'8314'_406
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.du_map_32
         (coe v2) (coe v0) (coe v1) (coe v3))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.++⁺ˡ
d_'43''43''8314''737'_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_'43''43''8314''737'_564 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'43''43''8314''737'_564
du_'43''43''8314''737'_564 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_'43''43''8314''737'_564
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_'43''43''737'_524
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.++⁺ʳ
d_'43''43''8314''691'_568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_'43''43''8314''691'_568 ~v0 ~v1 ~v2 v3 v4
  = du_'43''43''8314''691'_568 v3 v4
du_'43''43''8314''691'_568 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_'43''43''8314''691'_568 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_'43''43''691'_530
      (coe v0) (coe v1)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.++⁺
d_'43''43''8314'_570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_'43''43''8314'_570 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6
  = du_'43''43''8314'_570 v3 v4
du_'43''43''8314'_570 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_'43''43''8314'_570 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_'43''43''8314'_488
      (coe v0) (coe v1)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.++⁻
d_'43''43''8315'_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_'43''43''8315'_572 ~v0 ~v1 ~v2 v3 v4 ~v5 v6
  = du_'43''43''8315'_572 v3 v4 v6
du_'43''43''8315'_572 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_'43''43''8315'_572 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_'43''43''8315'_504
      (coe v0) (coe v1) (coe v2) v4
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.concat⁺
d_concat'8314'_578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [[AgdaAny]] ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_concat'8314'_578 ~v0 ~v1 ~v2 v3 v4 = du_concat'8314'_578 v3 v4
du_concat'8314'_578 ::
  [[AgdaAny]] ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_concat'8314'_578 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_concat'8314'_546
      (coe v0) (coe v1)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._._._∈_
d__'8712'__582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [[AgdaAny]] -> ()
d__'8712'__582 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.xs∈xss⇒xs⊆concat[xss]
d_xs'8712'xss'8658'xs'8838'concat'91'xss'93'_590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_xs'8712'xss'8658'xs'8838'concat'91'xss'93'_590 ~v0 ~v1 v2 v3 v4
                                                 v5
  = du_xs'8712'xss'8658'xs'8838'concat'91'xss'93'_590 v2 v3 v4 v5
du_xs'8712'xss'8658'xs'8838'concat'91'xss'93'_590 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_xs'8712'xss'8658'xs'8838'concat'91'xss'93'_590 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
              (coe
                 MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
                 (coe v0)) in
    coe
      (let v5
             = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v4) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_start_76
               (coe v5))
            v1 (coe MAlonzo.Code.Data.List.Base.du_concat_244 v2)
            (let v6
                   = coe
                       MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
                       (coe
                          MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
                          (coe v0)) in
             coe
               (let v7
                      = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v6) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                        (coe v7))
                     (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                           (coe v7)))
                     v1
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                     (coe MAlonzo.Code.Data.List.Base.du_concat_244 v2)
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8838'_316
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8818''45'go_96
                           (coe
                              MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_isPreorder_1316
                              (coe
                                 MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'isPreorder_40
                                 (coe v0))))
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                        (coe MAlonzo.Code.Data.List.Base.du_concat_244 v2)
                        (coe MAlonzo.Code.Data.List.Base.du_concat_244 v2)
                        (let v8
                               = coe
                                   MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_preorder_1464
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
                                      (coe v0)) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158
                                      (coe v8) in
                            coe
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                    (coe v9))
                                 (coe MAlonzo.Code.Data.List.Base.du_concat_244 v2))))
                        (coe
                           du_concat'8314'_578
                           (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1)) v2
                           (coe
                              MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.du_map_32
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Binary.Sublist.Setoid.du_'8838''45'reflexive_202)
                              (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                              (coe v2)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.du_fromAny_74
                                 (coe v2) (coe v3)))))
                     (let v8
                            = coe
                                MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                                (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v8))
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.all⊆concat
d_all'8838'concat_606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [[AgdaAny]] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_all'8838'concat_606 ~v0 ~v1 v2 v3 = du_all'8838'concat_606 v2 v3
du_all'8838'concat_606 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [[AgdaAny]] -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_all'8838'concat_606 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.du_tabulate'8347'_258
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
         (coe v0))
      (coe v1)
      (coe
         (\ v2 ->
            coe
              du_xs'8712'xss'8658'xs'8838'concat'91'xss'93'_590 (coe v0) (coe v2)
              (coe v1)))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.take⁺
d_take'8314'_612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  Integer ->
  Integer ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_take'8314'_612 ~v0 ~v1 v2 ~v3 v4 v5 v6
  = du_take'8314'_612 v2 v4 v5 v6
du_take'8314'_612 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  Integer ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_take'8314'_612 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_take'8314'_556
      (coe v1) (coe v2) (coe v2) (coe v3)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
            (coe
               MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
               (coe v0)))
         v2)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.drop⁺
d_drop'8314'_620 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  Integer ->
  Integer ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_drop'8314'_620 ~v0 ~v1 ~v2 v3 ~v4 v5 v6
  = du_drop'8314'_620 v3 v5 v6
du_drop'8314'_620 ::
  Integer ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_drop'8314'_620 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_drop'8314'_568
      (coe v0) (coe v1) (coe v2)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.drop⁺-≥
d_drop'8314''45''8805'_626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  Integer ->
  Integer ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_drop'8314''45''8805'_626 ~v0 ~v1 v2 v3 ~v4 v5 v6
  = du_drop'8314''45''8805'_626 v2 v3 v5 v6
du_drop'8314''45''8805'_626 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  Integer ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_drop'8314''45''8805'_626 v0 v1 v2 v3
  = coe
      du_drop'8314'_620 v1 v2 v2 v3
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_refl_1116
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
         (coe v2))
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.drop⁺-⊆
d_drop'8314''45''8838'_636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_drop'8314''45''8838'_636 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_drop'8314''45''8838'_636 v3 v4 v5 v6
du_drop'8314''45''8838'_636 ::
  [AgdaAny] ->
  [AgdaAny] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_drop'8314''45''8838'_636 v0 v1 v2 v3
  = coe
      du_drop'8314'_620 v2 v0 v1
      (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2814 (coe v2))
      v3
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.takeWhile⁺
d_takeWhile'8314'_660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_takeWhile'8314'_660 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 ~v10
  = du_takeWhile'8314'_660 v2 v7 v8 v9
du_takeWhile'8314'_660 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_takeWhile'8314'_660 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_'8838''45'takeWhile'45'Sublist_628
      (coe v1) (coe v2) (coe v3) (coe v3)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
            (coe
               MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
               (coe v0)))
         v3)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.dropWhile⁺
d_dropWhile'8314'_672 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_dropWhile'8314'_672 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 ~v10
  = du_dropWhile'8314'_672 v2 v7 v8 v9
du_dropWhile'8314'_672 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_dropWhile'8314'_672 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_'8839''45'dropWhile'45'Sublist_700
      (coe v1) (coe v2) (coe v3) (coe v3)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
            (coe
               MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
               (coe v0)))
         v3)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.filter⁺
d_filter'8314'_694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_filter'8314'_694 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_filter'8314'_694 v7 v8 v9 v10
du_filter'8314'_694 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_filter'8314'_694 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_'8838''45'filter'45'Sublist_786
      (coe v0) (coe v1) (coe v2) (coe v3) v5
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.reverseAcc⁺
d_reverseAcc'8314'_700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_reverseAcc'8314'_700 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6
  = du_reverseAcc'8314'_700 v3 v4
du_reverseAcc'8314'_700 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_reverseAcc'8314'_700 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_reverseAcc'8314'_978
      (coe v0) (coe v1)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.ʳ++⁺
d_'691''43''43''8314'_702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_'691''43''43''8314'_702 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6
  = du_'691''43''43''8314'_702 v3 v4
du_'691''43''43''8314'_702 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_'691''43''43''8314'_702 v0 v1
  = coe du_reverseAcc'8314'_700 (coe v0) (coe v1)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.reverse⁺
d_reverse'8314'_704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_reverse'8314'_704 ~v0 ~v1 ~v2 v3 v4 = du_reverse'8314'_704 v3 v4
du_reverse'8314'_704 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_reverse'8314'_704 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_reverse'8314'_996
      (coe v0) (coe v1)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.reverse⁻
d_reverse'8315'_706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_reverse'8315'_706 ~v0 ~v1 ~v2 v3 v4 = du_reverse'8315'_706 v3 v4
du_reverse'8315'_706 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_reverse'8315'_706 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_reverse'8315'_1000
      (coe v0) (coe v1)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.⊆-mergeˡ
d_'8838''45'merge'737'_722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_'8838''45'merge'737'_722 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_'8838''45'merge'737'_722 v2 v5 v6 v7
du_'8838''45'merge'737'_722 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_'8838''45'merge'737'_722 v0 v1 v2 v3
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.du_minimum_48
             (coe v3)
      (:) v4 v5
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_refl_1116
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
                    (coe v2)
             (:) v6 v7
               -> let v8 = coe v1 v4 v6 in
                  coe
                    (let v9
                           = coe
                               du_'8838''45'merge'737'_722 (coe v0) (coe v1) (coe v5) (coe v3) in
                     coe
                       (let v10
                              = coe
                                  du_'8838''45'merge'737'_722 (coe v0) (coe v1) (coe v2) (coe v7) in
                        coe
                          (case coe v8 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                               -> if coe v11
                                    then coe
                                           seq (coe v12)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                 (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                    (coe v0))
                                                 v4)
                                              v9)
                                    else coe
                                           seq (coe v12)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36
                                              v10)
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.⊆-mergeʳ
d_'8838''45'merge'691'_770 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_'8838''45'merge'691'_770 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_'8838''45'merge'691'_770 v2 v5 v6 v7
du_'8838''45'merge'691'_770 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_'8838''45'merge'691'_770 v0 v1 v2 v3
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_refl_1116
             (coe
                MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                (coe
                   MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
             (coe v3)
      (:) v4 v5
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.du_minimum_48
                    (coe
                       MAlonzo.Code.Data.List.Base.du_merge_192 (coe v1) (coe v2)
                       (coe v3))
             (:) v6 v7
               -> let v8 = coe v1 v4 v6 in
                  coe
                    (let v9
                           = coe
                               du_'8838''45'merge'691'_770 (coe v0) (coe v1) (coe v5) (coe v3) in
                     coe
                       (let v10
                              = coe
                                  du_'8838''45'merge'691'_770 (coe v0) (coe v1) (coe v2) (coe v7) in
                        coe
                          (case coe v8 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                               -> if coe v11
                                    then coe
                                           seq (coe v12)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36
                                              v9)
                                    else coe
                                           seq (coe v12)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                 (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                    (coe v0))
                                                 v6)
                                              v10)
                             _ -> MAlonzo.RTE.mazUnreachableError)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.∷⁻¹
d_'8759''8315''185'_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1810
d_'8759''8315''185'_818 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8759''8315''185'_818 v6
du_'8759''8315''185'_818 ::
  [AgdaAny] ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1810
du_'8759''8315''185'_818 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_'8759''8315''185'_1026
      (coe v0)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.∷ʳ⁻¹
d_'8759''691''8315''185'_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1810
d_'8759''691''8315''185'_820 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8759''691''8315''185'_820
du_'8759''691''8315''185'_820 ::
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1810
du_'8759''691''8315''185'_820 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_'8759''691''8315''185'_1032
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.length-mono-≤
d_length'45'mono'45''8804'_826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_length'45'mono'45''8804'_826 ~v0 ~v1 ~v2 v3 v4
  = du_length'45'mono'45''8804'_826 v3 v4
du_length'45'mono'45''8804'_826 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_length'45'mono'45''8804'_826 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_length'45'mono'45''8804'_116
      (coe v0) (coe v1)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.to-≋
d_to'45''8779'_828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_to'45''8779'_828 ~v0 ~v1 ~v2 v3 v4 = du_to'45''8779'_828 v3 v4
du_to'45''8779'_828 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_to'45''8779'_828 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_toPointwise_132
      (coe v0) (coe v1) v3
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.[]⊆-universal
d_'91''93''8838''45'universal_832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_'91''93''8838''45'universal_832 ~v0 ~v1 ~v2
  = du_'91''93''8838''45'universal_832
du_'91''93''8838''45'universal_832 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_'91''93''8838''45'universal_832
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_Sublist'45''91''93''45'universal_1050
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.[]⊆-irrelevant
d_'91''93''8838''45'irrelevant_836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'91''93''8838''45'irrelevant_836 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._._._∈_
d__'8712'__844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> [AgdaAny] -> ()
d__'8712'__844 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.to∈-injective
d_to'8712''45'injective_850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_to'8712''45'injective_850 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.from∈-injective
d_from'8712''45'injective_856 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_from'8712''45'injective_856 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.to∈∘from∈≗id
d_to'8712''8728'from'8712''8791'id_860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_to'8712''8728'from'8712''8791'id_860 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.[x]⊆xs⤖x∈xs
d_'91'x'93''8838'xs'10518'x'8712'xs_862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Function.Bundles.T_Bijection_978
d_'91'x'93''8838'xs'10518'x'8712'xs_862 ~v0 ~v1 ~v2 ~v3 v4
  = du_'91'x'93''8838'xs'10518'x'8712'xs_862 v4
du_'91'x'93''8838'xs'10518'x'8712'xs_862 ::
  [AgdaAny] -> MAlonzo.Code.Function.Bundles.T_Bijection_978
du_'91'x'93''8838'xs'10518'x'8712'xs_862 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_Sublist'45''91'x'93''45'bijection_1102
      (coe v0)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._._∷ʳ-DisjointUnion³_
d__'8759''691''45'DisjointUnion'179'__866 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182
d__'8759''691''45'DisjointUnion'179'__866 ~v0 ~v1 ~v2
  = du__'8759''691''45'DisjointUnion'179'__866
du__'8759''691''45'DisjointUnion'179'__866 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182
du__'8759''691''45'DisjointUnion'179'__866 v0 v1 v2 v3 v4 v5 v6 v7
                                           v8 v9 v10 v11 v12 v13 v14
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du__'8759''691''45'DisjointUnion'179'__2258
      v14
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._._∷₁-DisjointUnion³_
d__'8759''8321''45'DisjointUnion'179'__868 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182
d__'8759''8321''45'DisjointUnion'179'__868 ~v0 ~v1 ~v2
  = du__'8759''8321''45'DisjointUnion'179'__868
du__'8759''8321''45'DisjointUnion'179'__868 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182
du__'8759''8321''45'DisjointUnion'179'__868 v0 v1 v2 v3 v4 v5 v6 v7
                                            v8 v9 v10 v11 v12 v13 v14 v15 v16
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du__'8759''8321''45'DisjointUnion'179'__2302
      v13 v15 v16
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._._∷₂-DisjointUnion³_
d__'8759''8322''45'DisjointUnion'179'__870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182
d__'8759''8322''45'DisjointUnion'179'__870 ~v0 ~v1 ~v2
  = du__'8759''8322''45'DisjointUnion'179'__870
du__'8759''8322''45'DisjointUnion'179'__870 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182
du__'8759''8322''45'DisjointUnion'179'__870 v0 v1 v2 v3 v4 v5 v6 v7
                                            v8 v9 v10 v11 v12 v13 v14 v15 v16
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du__'8759''8322''45'DisjointUnion'179'__2346
      v13 v15 v16
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._._∷₃-DisjointUnion³_
d__'8759''8323''45'DisjointUnion'179'__872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182
d__'8759''8323''45'DisjointUnion'179'__872 ~v0 ~v1 ~v2
  = du__'8759''8323''45'DisjointUnion'179'__872
du__'8759''8323''45'DisjointUnion'179'__872 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182
du__'8759''8323''45'DisjointUnion'179'__872 v0 v1 v2 v3 v4 v5 v6 v7
                                            v8 v9 v10 v11 v12 v13 v14 v15 v16
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du__'8759''8323''45'DisjointUnion'179'__2390
      v13 v15 v16
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.Disjoint-irrefl
d_Disjoint'45'irrefl_874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_Disjoint'45'irrefl_874 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.Disjoint-irrefl′
d_Disjoint'45'irrefl'8242'_876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_Disjoint'45'irrefl'8242'_876 ~v0 ~v1 ~v2
  = du_Disjoint'45'irrefl'8242'_876
du_Disjoint'45'irrefl'8242'_876 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_Disjoint'45'irrefl'8242'_876 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_Disjoint'45'irrefl'8242'_2016
      v1 v2 v3
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.Disjoint-irrelevant
d_Disjoint'45'irrelevant_878 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Disjoint'45'irrelevant_878 = erased
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.Disjoint-sym
d_Disjoint'45'sym_880 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130
d_Disjoint'45'sym_880 ~v0 ~v1 ~v2 = du_Disjoint'45'sym_880
du_Disjoint'45'sym_880 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130
du_Disjoint'45'sym_880
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_Disjoint'45'sym_2076
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.DisjointUnion-[]ʳ
d_DisjointUnion'45''91''93''691'_882 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198
d_DisjointUnion'45''91''93''691'_882 ~v0 ~v1 ~v2
  = du_DisjointUnion'45''91''93''691'_882
du_DisjointUnion'45''91''93''691'_882 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198
du_DisjointUnion'45''91''93''691'_882
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_DisjointUnion'45''91''93''691'_2122
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.DisjointUnion-[]ˡ
d_DisjointUnion'45''91''93''737'_884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198
d_DisjointUnion'45''91''93''737'_884 ~v0 ~v1 ~v2
  = du_DisjointUnion'45''91''93''737'_884
du_DisjointUnion'45''91''93''737'_884 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198
du_DisjointUnion'45''91''93''737'_884
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_DisjointUnion'45''91''93''737'_2098
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.DisjointUnion-fromAny∘toAny-∷ˡ⁻
d_DisjointUnion'45'fromAny'8728'toAny'45''8759''737''8315'_886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198
d_DisjointUnion'45'fromAny'8728'toAny'45''8759''737''8315'_886 ~v0
                                                               ~v1 ~v2
  = du_DisjointUnion'45'fromAny'8728'toAny'45''8759''737''8315'_886
du_DisjointUnion'45'fromAny'8728'toAny'45''8759''737''8315'_886 ::
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198
du_DisjointUnion'45'fromAny'8728'toAny'45''8759''737''8315'_886 v0
                                                                v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_DisjointUnion'45'fromAny'8728'toAny'45''8759''737''8315'_2146
      v1 v2 v3
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.DisjointUnion-sym
d_DisjointUnion'45'sym_888 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198
d_DisjointUnion'45'sym_888 ~v0 ~v1 ~v2
  = du_DisjointUnion'45'sym_888
du_DisjointUnion'45'sym_888 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198
du_DisjointUnion'45'sym_888
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_DisjointUnion'45'sym_2052
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.DisjointUnion³
d_DisjointUnion'179'_890 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                         a13 a14 a15
  = ()
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.DisjointUnion→Disjoint
d_DisjointUnion'8594'Disjoint_892 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130
d_DisjointUnion'8594'Disjoint_892 ~v0 ~v1 ~v2
  = du_DisjointUnion'8594'Disjoint_892
du_DisjointUnion'8594'Disjoint_892 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130
du_DisjointUnion'8594'Disjoint_892
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_DisjointUnion'8594'Disjoint_1876
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.Disjoint→DisjointUnion
d_Disjoint'8594'DisjointUnion_894 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Disjoint'8594'DisjointUnion_894 ~v0 ~v1 ~v2
  = du_Disjoint'8594'DisjointUnion_894
du_Disjoint'8594'DisjointUnion_894 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Disjoint'8594'DisjointUnion_894
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_Disjoint'8594'DisjointUnion_1904
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.disjointUnion³
d_disjointUnion'179'_896 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182
d_disjointUnion'179'_896 ~v0 ~v1 ~v2 = du_disjointUnion'179'_896
du_disjointUnion'179'_896 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182
du_disjointUnion'179'_896
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_disjointUnion'179'_2428
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.disjoint⇒disjoint-to-union
d_disjoint'8658'disjoint'45'to'45'union_898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130
d_disjoint'8658'disjoint'45'to'45'union_898 ~v0 ~v1 ~v2
  = du_disjoint'8658'disjoint'45'to'45'union_898
du_disjoint'8658'disjoint'45'to'45'union_898 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130
du_disjoint'8658'disjoint'45'to'45'union_898
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_disjoint'8658'disjoint'45'to'45'union_2494
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.⊆-disjoint?
d_'8838''45'disjoint'63'_900 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8838''45'disjoint'63'_900 ~v0 ~v1 ~v2
  = du_'8838''45'disjoint'63'_900
du_'8838''45'disjoint'63'_900 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8838''45'disjoint'63'_900
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_'8838''45'disjoint'63'_1928
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.DisjointUnion³.join₁
d_join'8321'_904 ::
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198
d_join'8321'_904 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.d_join'8321'_2224
      (coe v0)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.DisjointUnion³.join₂
d_join'8322'_906 ::
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198
d_join'8322'_906 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.d_join'8322'_2226
      (coe v0)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.DisjointUnion³.join₃
d_join'8323'_908 ::
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198
d_join'8323'_908 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.d_join'8323'_2228
      (coe v0)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.DisjointUnion³.sub³
d_sub'179'_910 ::
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_sub'179'_910 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.d_sub'179'_2222
      (coe v0)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.DisjointUnion³.union³
d_union'179'_912 ::
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.T_DisjointUnion'179'_2182 ->
  [AgdaAny]
d_union'179'_912 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.d_union'179'_2220
      (coe v0)
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.shrinkDisjoint
d_shrinkDisjoint_916 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130
d_shrinkDisjoint_916 ~v0 ~v1 ~v2 = du_shrinkDisjoint_916
du_shrinkDisjoint_916 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130
du_shrinkDisjoint_916
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_shrinkDisjoint_2638
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.weakenDisjoint
d_weakenDisjoint_918 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130
d_weakenDisjoint_918 ~v0 ~v1 ~v2 = du_weakenDisjoint_918
du_weakenDisjoint_918 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130
du_weakenDisjoint_918
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_weakenDisjoint_2590
-- Data.List.Relation.Binary.Sublist.Setoid.Properties._.weakenDisjointUnion
d_weakenDisjointUnion_920 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198
d_weakenDisjointUnion_920 ~v0 ~v1 ~v2 = du_weakenDisjointUnion_920
du_weakenDisjointUnion_920 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_DisjointUnion_198
du_weakenDisjointUnion_920
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Properties.du_weakenDisjointUnion_2546
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.shrinkDisjointˡ
d_shrinkDisjoint'737'_936 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130
d_shrinkDisjoint'737'_936 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_shrinkDisjoint'737'_936 v3 v4 v5 v6 v7 v8 v9 v10
du_shrinkDisjoint'737'_936 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130
du_shrinkDisjoint'737'_936 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C_'91''93'_132
        -> coe seq (coe v6) (coe v7)
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C__'8759''8345'__146 v14
        -> case coe v2 of
             (:) v15 v16
               -> case coe v4 of
                    MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v20
                      -> case coe v5 of
                           MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v24
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C__'8759''8345'__146
                                  (coe
                                     du_shrinkDisjoint'737'_936 (coe v0) (coe v1) (coe v16) (coe v3)
                                     (coe v20) (coe v24) (coe v6) (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C__'8759''8343'__164 v16
        -> case coe v0 of
             (:) v17 v18
               -> case coe v2 of
                    (:) v19 v20
                      -> case coe v4 of
                           MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46 v25 v26
                             -> case coe v5 of
                                  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v30
                                    -> case coe v6 of
                                         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v34
                                           -> coe
                                                MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C__'8759''8345'__146
                                                (coe
                                                   du_shrinkDisjoint'737'_936 (coe v18) (coe v1)
                                                   (coe v20) (coe v3) (coe v26) (coe v30) (coe v34)
                                                   (coe v16))
                                         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46 v35 v36
                                           -> case coe v3 of
                                                (:) v37 v38
                                                  -> coe
                                                       MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C__'8759''8343'__164
                                                       (coe
                                                          du_shrinkDisjoint'737'_936 (coe v18)
                                                          (coe v1) (coe v20) (coe v38) (coe v26)
                                                          (coe v30) (coe v36) (coe v16))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C__'8759''7523'__182 v16
        -> case coe v1 of
             (:) v17 v18
               -> case coe v2 of
                    (:) v19 v20
                      -> case coe v4 of
                           MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v24
                             -> case coe v5 of
                                  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46 v29 v30
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C__'8759''7523'__182
                                         (coe
                                            du_shrinkDisjoint'737'_936 (coe v0) (coe v18) (coe v20)
                                            (coe v3) (coe v24) (coe v30) (coe v6) (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Setoid.Properties.shrinkDisjointʳ
d_shrinkDisjoint'691'_980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130
d_shrinkDisjoint'691'_980 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_shrinkDisjoint'691'_980 v3 v4 v5 v6 v7 v8 v9 v10
du_shrinkDisjoint'691'_980 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.T_Disjoint_130
du_shrinkDisjoint'691'_980 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v7 of
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C_'91''93'_132
        -> coe seq (coe v6) (coe v7)
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C__'8759''8345'__146 v14
        -> case coe v2 of
             (:) v15 v16
               -> case coe v4 of
                    MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v20
                      -> case coe v5 of
                           MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v24
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C__'8759''8345'__146
                                  (coe
                                     du_shrinkDisjoint'691'_980 (coe v0) (coe v1) (coe v16) (coe v3)
                                     (coe v20) (coe v24) (coe v6) (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C__'8759''8343'__164 v16
        -> case coe v0 of
             (:) v17 v18
               -> case coe v2 of
                    (:) v19 v20
                      -> case coe v4 of
                           MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46 v25 v26
                             -> case coe v5 of
                                  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v30
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C__'8759''8343'__164
                                         (coe
                                            du_shrinkDisjoint'691'_980 (coe v18) (coe v1) (coe v20)
                                            (coe v3) (coe v26) (coe v30) (coe v6) (coe v16))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C__'8759''7523'__182 v16
        -> case coe v1 of
             (:) v17 v18
               -> case coe v2 of
                    (:) v19 v20
                      -> case coe v4 of
                           MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v24
                             -> case coe v5 of
                                  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46 v29 v30
                                    -> case coe v6 of
                                         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v34
                                           -> coe
                                                MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C__'8759''8345'__146
                                                (coe
                                                   du_shrinkDisjoint'691'_980 (coe v0) (coe v18)
                                                   (coe v20) (coe v3) (coe v24) (coe v30) (coe v34)
                                                   (coe v16))
                                         MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46 v35 v36
                                           -> case coe v3 of
                                                (:) v37 v38
                                                  -> coe
                                                       MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.C__'8759''7523'__182
                                                       (coe
                                                          du_shrinkDisjoint'691'_980 (coe v0)
                                                          (coe v18) (coe v20) (coe v38) (coe v24)
                                                          (coe v30) (coe v36) (coe v16))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
