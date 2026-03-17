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

module MAlonzo.Code.Relation.Binary.Reasoning.PartialOrder where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Relation.Binary.Reasoning.PartialOrder._._IsRelatedTo_
d__IsRelatedTo__140 a0 a1 a2 a3 a4 a5 = ()
-- Relation.Binary.Reasoning.PartialOrder._._∎
d__'8718'_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d__'8718'_142 ~v0 ~v1 ~v2 v3 = du__'8718'_142 v3
du__'8718'_142 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du__'8718'_142 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                 (coe v0)) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
            (coe v1)))
-- Relation.Binary.Reasoning.PartialOrder._.<-go
d_'60''45'go_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'60''45'go_144 ~v0 ~v1 ~v2 v3 = du_'60''45'go_144 v3
du_'60''45'go_144 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'60''45'go_144 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
      (coe
         MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45'trans_202
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
            (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45'resp'45''8776'_328
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                  (coe v0))))
         (let v1
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_preorder_510 (coe v0) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v1)))))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45''8804''45'trans_256
         (let v1
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_preorder_510 (coe v0) in
          coe
            (let v2
                   = coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_setoid_184 (coe v1) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v2)))))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_84
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                  (coe v0))))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_antisym_246
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
               (coe v0)))
         (let v1
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_preorder_510 (coe v0) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v1)))))
-- Relation.Binary.Reasoning.PartialOrder._.IsEquality
d_IsEquality_146 a0 a1 a2 a3 a4 a5 a6 = ()
-- Relation.Binary.Reasoning.PartialOrder._.IsEquality?
d_IsEquality'63'_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsEquality'63'_148 ~v0 ~v1 ~v2 ~v3 = du_IsEquality'63'_148
du_IsEquality'63'_148 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_IsEquality'63'_148 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsEquality'63'_224
      v2
-- Relation.Binary.Reasoning.PartialOrder._.IsStrict
d_IsStrict_150 a0 a1 a2 a3 a4 a5 a6 = ()
-- Relation.Binary.Reasoning.PartialOrder._.IsStrict?
d_IsStrict'63'_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsStrict'63'_152 ~v0 ~v1 ~v2 ~v3 = du_IsStrict'63'_152
du_IsStrict'63'_152 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_IsStrict'63'_152 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsStrict'63'_188
      v2
-- Relation.Binary.Reasoning.PartialOrder._.begin_
d_begin__154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny
d_begin__154 ~v0 ~v1 ~v2 v3 = du_begin__154 v3
du_begin__154 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny
du_begin__154 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                 (coe v0)) in
    coe
      (let v2
             = \ v2 v3 v4 ->
                 coe
                   MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''8658''8804'_32
                   v4 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
               (coe v1) (coe v2))))
-- Relation.Binary.Reasoning.PartialOrder._.begin-contradiction_
d_begin'45'contradiction__156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny
d_begin'45'contradiction__156 ~v0 ~v1 ~v2 ~v3
  = du_begin'45'contradiction__156
du_begin'45'contradiction__156 ::
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny
du_begin'45'contradiction__156 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__246
-- Relation.Binary.Reasoning.PartialOrder._.begin_
d_begin__158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> AgdaAny
d_begin__158 ~v0 ~v1 ~v2 ~v3 = du_begin__158
du_begin__158 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> AgdaAny
du_begin__158
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
           (coe v0) v1 v2 v3)
-- Relation.Binary.Reasoning.PartialOrder._.begin_
d_begin__160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_begin__160 ~v0 ~v1 ~v2 ~v3 = du_begin__160
du_begin__160 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_begin__160
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
           (coe v0) v1 v2 v3)
-- Relation.Binary.Reasoning.PartialOrder._.eqRelation
d_eqRelation_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_eqRelation_162 ~v0 ~v1 ~v2 ~v3 = du_eqRelation_162
du_eqRelation_162 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
du_eqRelation_162
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238
-- Relation.Binary.Reasoning.PartialOrder._.extractEquality
d_extractEquality_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsEquality_208 ->
  AgdaAny
d_extractEquality_166 ~v0 ~v1 ~v2 ~v3 = du_extractEquality_166
du_extractEquality_166 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsEquality_208 ->
  AgdaAny
du_extractEquality_166 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_extractEquality_234
      v2 v3
-- Relation.Binary.Reasoning.PartialOrder._.extractStrict
d_extractStrict_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsStrict_172 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_extractStrict_168 ~v0 ~v1 ~v2 ~v3 = du_extractStrict_168
du_extractStrict_168 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsStrict_172 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_extractStrict_168 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_extractStrict_198
      v2 v3
-- Relation.Binary.Reasoning.PartialOrder._.start
d_start_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny
d_start_176 ~v0 ~v1 ~v2 v3 = du_start_176 v3
du_start_176 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny
du_start_176 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
            (coe v0)))
      (\ v1 v2 v3 ->
         coe
           MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''8658''8804'_32
           v3)
-- Relation.Binary.Reasoning.PartialOrder._.step-<
d_step'45''60'_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''60'_178 ~v0 ~v1 ~v2 v3 = du_step'45''60'_178 v3
du_step'45''60'_178 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''60'_178 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45'trans_202
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                 (coe v0)) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45'resp'45''8776'_328
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                          (coe v0))))
                 (let v2
                        = coe
                            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_510 (coe v0) in
                  coe
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158
                          (coe v2)))) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45''8804''45'trans_256
                    (let v3
                           = coe
                               MAlonzo.Code.Relation.Binary.Bundles.du_preorder_510 (coe v0) in
                     coe
                       (let v4
                              = coe
                                  MAlonzo.Code.Relation.Binary.Bundles.du_setoid_184 (coe v3) in
                        coe
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (coe v4)))))
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_trans_84
                       (coe
                          MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                             (coe v0))))
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_antisym_246
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                          (coe v0)))
                    (let v3
                           = coe
                               MAlonzo.Code.Relation.Binary.Bundles.du_preorder_510 (coe v0) in
                     coe
                       (coe
                          MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158
                             (coe v3)))) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe v1) (coe v2) (coe v3)))))
-- Relation.Binary.Reasoning.PartialOrder._.step-≈
d_step'45''8776'_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8776'_180 ~v0 ~v1 ~v2 v3 = du_step'45''8776'_180 v3
du_step'45''8776'_180 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8776'_180 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                 (coe v0)) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45'resp'45''8776'_328
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                          (coe v0))))
                 (let v2
                        = coe
                            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_510 (coe v0) in
                  coe
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158
                          (coe v2)))) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776'_372
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe v1) (coe v2))))
-- Relation.Binary.Reasoning.PartialOrder._.step-≈-⟨
d_step'45''8776''45''10216'_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8776''45''10216'_182 ~v0 ~v1 ~v2 v3
  = du_step'45''8776''45''10216'_182 v3
du_step'45''8776''45''10216'_182 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8776''45''10216'_182 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                 (coe v0)) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45'resp'45''8776'_328
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                          (coe v0))))
                 (let v2
                        = coe
                            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_510 (coe v0) in
                  coe
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158
                          (coe v2)))) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe v1) (coe v2))
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                  (coe v1)))))
-- Relation.Binary.Reasoning.PartialOrder._.step-≈-⟩
d_step'45''8776''45''10217'_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8776''45''10217'_184 ~v0 ~v1 ~v2 v3
  = du_step'45''8776''45''10217'_184 v3
du_step'45''8776''45''10217'_184 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8776''45''10217'_184 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                 (coe v0)) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45'resp'45''8776'_328
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                          (coe v0))))
                 (let v2
                        = coe
                            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_510 (coe v0) in
                  coe
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158
                          (coe v2)))) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe v1) (coe v2))))
-- Relation.Binary.Reasoning.PartialOrder._.step-≈˘
d_step'45''8776''728'_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8776''728'_186 ~v0 ~v1 ~v2 v3
  = du_step'45''8776''728'_186 v3
du_step'45''8776''728'_186 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8776''728'_186 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                 (coe v0)) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45'resp'45''8776'_328
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                          (coe v0))))
                 (let v2
                        = coe
                            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_510 (coe v0) in
                  coe
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158
                          (coe v2)))) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''728'_374
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe v1) (coe v2))
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                  (coe v1)))))
-- Relation.Binary.Reasoning.PartialOrder._.step-≡
d_step'45''8801'_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801'_188 ~v0 ~v1 ~v2 ~v3 = du_step'45''8801'_188
du_step'45''8801'_188 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801'_188
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.PartialOrder._.step-≡-∣
d_step'45''8801''45''8739'_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''8739'_190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_step'45''8801''45''8739'_190 v6
du_step'45''8801''45''8739'_190 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''45''8739'_190 v0 = coe v0
-- Relation.Binary.Reasoning.PartialOrder._.step-≡-⟨
d_step'45''8801''45''10216'_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10216'_192 ~v0 ~v1 ~v2 ~v3
  = du_step'45''8801''45''10216'_192
du_step'45''8801''45''10216'_192 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''45''10216'_192
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.PartialOrder._.step-≡-⟩
d_step'45''8801''45''10217'_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10217'_194 ~v0 ~v1 ~v2 ~v3
  = du_step'45''8801''45''10217'_194
du_step'45''8801''45''10217'_194 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''45''10217'_194
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.PartialOrder._.step-≡˘
d_step'45''8801''728'_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''728'_196 ~v0 ~v1 ~v2 ~v3
  = du_step'45''8801''728'_196
du_step'45''8801''728'_196 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''728'_196
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.PartialOrder._.step-≤
d_step'45''8804'_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8804'_198 ~v0 ~v1 ~v2 v3 = du_step'45''8804'_198 v3
du_step'45''8804'_198 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8804'_198 v0
  = let v1
          = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                 (coe v0)) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'8804''45''60''45'trans_274
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_trans_84
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                          (coe v0))))
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_antisym_246
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                       (coe v0)))
                 (let v2
                        = coe
                            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_510 (coe v0) in
                  coe
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158
                          (coe v2)))) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe v1) (coe v2))))
-- Relation.Binary.Reasoning.PartialOrder._.stop
d_stop_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_stop_200 ~v0 ~v1 ~v2 v3 = du_stop_200 v3
du_stop_200 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_stop_200 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
            (coe v0)))
-- Relation.Binary.Reasoning.PartialOrder._.strictRelation
d_strictRelation_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_strictRelation_204 ~v0 ~v1 ~v2 ~v3 = du_strictRelation_204
du_strictRelation_204 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
du_strictRelation_204
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202
-- Relation.Binary.Reasoning.PartialOrder._.≈-go
d_'8776''45'go_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8776''45'go_206 ~v0 ~v1 ~v2 v3 = du_'8776''45'go_206 v3
du_'8776''45'go_206 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'8776''45'go_206 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
            (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'60''45'resp'45''8776'_328
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                  (coe v0))))
         (let v1
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_preorder_510 (coe v0) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v1)))))
-- Relation.Binary.Reasoning.PartialOrder._.≡-go
d_'8801''45'go_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8801''45'go_208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8801''45'go_208 v8
du_'8801''45'go_208 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'8801''45'go_208 v0 = coe v0
-- Relation.Binary.Reasoning.PartialOrder._.≤-go
d_'8804''45'go_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8804''45'go_210 ~v0 ~v1 ~v2 v3 = du_'8804''45'go_210 v3
du_'8804''45'go_210 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'8804''45'go_210 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
            (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.NonStrictToStrict.du_'8804''45''60''45'trans_274
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_84
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_244
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
                  (coe v0))))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_antisym_246
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_502
               (coe v0)))
         (let v1
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_preorder_510 (coe v0) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_158 (coe v1)))))
