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

module MAlonzo.Code.Algebra.Morphism.RingMonomorphism where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Morphism.GroupMonomorphism
import qualified MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism
import qualified MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism
import qualified MAlonzo.Code.Algebra.Morphism.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Morphism.RingMonomorphism._._*_
d__'42'__68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'42'__68 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 = du__'42'__68 v4
du__'42'__68 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'42'__68 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 (coe v0)
-- Algebra.Morphism.RingMonomorphism._._+_
d__'43'__70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'43'__70 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 = du__'43'__70 v4
du__'43'__70 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'43'__70 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 (coe v0)
-- Algebra.Morphism.RingMonomorphism._._≈_
d__'8776'__72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__72 = erased
-- Algebra.Morphism.RingMonomorphism._.-_
d_'45'__86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  AgdaAny -> AgdaAny
d_'45'__86 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 = du_'45'__86 v4
du_'45'__86 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  AgdaAny -> AgdaAny
du_'45'__86 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 (coe v0)
-- Algebra.Morphism.RingMonomorphism._.0#
d_0'35'_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  AgdaAny
d_0'35'_88 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 = du_0'35'_88 v4
du_0'35'_88 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 -> AgdaAny
du_0'35'_88 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)
-- Algebra.Morphism.RingMonomorphism._.1#
d_1'35'_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  AgdaAny
d_1'35'_90 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 = du_1'35'_90 v4
du_1'35'_90 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 -> AgdaAny
du_1'35'_90 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_1'35'_308 (coe v0)
-- Algebra.Morphism.RingMonomorphism._._≈_
d__'8776'__100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__100 = erased
-- Algebra.Morphism.RingMonomorphism._._+_
d__'43'__104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'43'__104 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du__'43'__104 v5
du__'43'__104 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'43'__104 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 (coe v0)
-- Algebra.Morphism.RingMonomorphism._._*_
d__'42'__106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'42'__106 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du__'42'__106 v5
du__'42'__106 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'42'__106 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 (coe v0)
-- Algebra.Morphism.RingMonomorphism._.0#
d_0'35'_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  AgdaAny
d_0'35'_118 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du_0'35'_118 v5
du_0'35'_118 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 -> AgdaAny
du_0'35'_118 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)
-- Algebra.Morphism.RingMonomorphism._.1#
d_1'35'_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  AgdaAny
d_1'35'_120 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du_1'35'_120 v5
du_1'35'_120 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 -> AgdaAny
du_1'35'_120 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_1'35'_308 (coe v0)
-- Algebra.Morphism.RingMonomorphism._.-_
d_'45'__128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  AgdaAny -> AgdaAny
d_'45'__128 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du_'45'__128 v5
du_'45'__128 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  AgdaAny -> AgdaAny
du_'45'__128 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 (coe v0)
-- Algebra.Morphism.RingMonomorphism._.assoc
d_assoc_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_132 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_assoc_132 v4 v5 v6 v7
du_assoc_132 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_132 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (let v7
                   = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4) in
             coe
               (let v8
                      = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5) in
                coe
                  (let v9
                         = coe
                             MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                             (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_assoc_160
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v7))
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v8))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                           (coe v9))))))))
-- Algebra.Morphism.RingMonomorphism._.cancel
d_cancel_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cancel_134 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cancel_134 v4 v5 v6 v7
du_cancel_134 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cancel_134 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (let v7
                   = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4) in
             coe
               (let v8
                      = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5) in
                coe
                  (let v9
                         = coe
                             MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                             (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel_236
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v7))
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v8))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                           (coe v9))))))))
-- Algebra.Morphism.RingMonomorphism._.cancelʳ
d_cancel'691'_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'691'_136 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cancel'691'_136 v4 v5 v6 v7
du_cancel'691'_136 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'691'_136 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (let v7
                   = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4) in
             coe
               (let v8
                      = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5) in
                coe
                  (let v9
                         = coe
                             MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                             (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel'691'_224
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v7))
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v8))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                           (coe v9))))))))
-- Algebra.Morphism.RingMonomorphism._.cancelˡ
d_cancel'737'_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'737'_138 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cancel'737'_138 v4 v5 v6 v7
du_cancel'737'_138 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'737'_138 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (let v7
                   = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4) in
             coe
               (let v8
                      = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5) in
                coe
                  (let v9
                         = coe
                             MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                             (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel'737'_212
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v7))
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v8))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                           (coe v9))))))))
-- Algebra.Morphism.RingMonomorphism._.comm
d_comm_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_140 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_comm_140 v4 v5 v6 v7
du_comm_140 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_140 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (let v7
                   = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4) in
             coe
               (let v8
                      = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5) in
                coe
                  (let v9
                         = coe
                             MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                             (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_comm_170
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v7))
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v8))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                           (coe v9))))))))
-- Algebra.Morphism.RingMonomorphism._.cong
d_cong_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_142 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_cong_142 v4 v5 v6 v7
du_cong_142 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cong_142 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (let v7
                   = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4) in
             coe
               (let v8
                      = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5) in
                coe
                  (let v9
                         = coe
                             MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                             (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cong_146
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v7))
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v8))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                           (coe v9))))))))
-- Algebra.Morphism.RingMonomorphism._.idem
d_idem_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_idem_144 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_idem_144 v4 v5 v6 v7
du_idem_144 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_idem_144 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (let v7
                   = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4) in
             coe
               (let v8
                      = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5) in
                coe
                  (let v9
                         = coe
                             MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                             (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_idem_178
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v7))
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v8))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                           (coe v9))))))))
-- Algebra.Morphism.RingMonomorphism._.identity
d_identity_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_146 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_identity_146 v4 v5 v6 v7
du_identity_146 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_146 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_identity_176
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.identityʳ
d_identity'691'_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_identity'691'_148 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_identity'691'_148 v4 v5 v6 v7
du_identity'691'_148 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_identity'691'_148 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_identity'691'_170
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.identityˡ
d_identity'737'_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_identity'737'_150 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_identity'737'_150 v4 v5 v6 v7
du_identity'737'_150 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_identity'737'_150 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_identity'737'_164
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.isBand
d_isBand_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506
d_isBand_152 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isBand_152 v4 v5 v6 v7
du_isBand_152 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506
du_isBand_152 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (let v7
                   = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4) in
             coe
               (let v8
                      = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5) in
                coe
                  (let v9
                         = coe
                             MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                             (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isBand_302
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v7))
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v8))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                           (coe v9))))))))
-- Algebra.Morphism.RingMonomorphism._.isCommutativeMonoid
d_isCommutativeMonoid_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_isCommutativeMonoid_154 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isCommutativeMonoid_154 v4 v5 v6 v7
du_isCommutativeMonoid_154 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_isCommutativeMonoid_154 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_isCommutativeMonoid_236
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.isMagma
d_isMagma_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_156 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isMagma_156 v4 v5 v6 v7
du_isMagma_156 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_156 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (let v7
                   = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4) in
             coe
               (let v8
                      = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5) in
                coe
                  (let v9
                         = coe
                             MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                             (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isMagma_238
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v7))
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v8))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                           (coe v9))))))))
-- Algebra.Morphism.RingMonomorphism._.isMonoid
d_isMonoid_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_158 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isMonoid_158 v4 v5 v6 v7
du_isMonoid_158 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_isMonoid_158 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_isMonoid_192
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.isSelectiveMagma
d_isSelectiveMagma_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434
d_isSelectiveMagma_160 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isSelectiveMagma_160 v4 v5 v6 v7
du_isSelectiveMagma_160 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434
du_isSelectiveMagma_160 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (let v7
                   = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4) in
             coe
               (let v8
                      = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5) in
                coe
                  (let v9
                         = coe
                             MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                             (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isSelectiveMagma_340
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v7))
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v8))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                           (coe v9))))))))
-- Algebra.Morphism.RingMonomorphism._.isSemigroup
d_isSemigroup_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_162 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isSemigroup_162 v4 v5 v6 v7
du_isSemigroup_162 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_162 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (let v7
                   = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4) in
             coe
               (let v8
                      = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5) in
                coe
                  (let v9
                         = coe
                             MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                             (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isSemigroup_268
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v7))
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v8))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                           (coe v9))))))))
-- Algebra.Morphism.RingMonomorphism._.sel
d_sel_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_164 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_sel_164 v4 v5 v6 v7
du_sel_164 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sel_164 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (let v7
                   = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4) in
             coe
               (let v8
                      = coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5) in
                coe
                  (let v9
                         = coe
                             MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                             (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_sel_184
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v7))
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v8))
                        (coe v2)
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                           (coe v9))))))))
-- Algebra.Morphism.RingMonomorphism._.zero
d_zero_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_166 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_zero_166 v4 v5 v6 v7
du_zero_166 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_166 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_zero_190
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.zeroʳ
d_zero'691'_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_zero'691'_168 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_zero'691'_168 v4 v5 v6 v7
du_zero'691'_168 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_zero'691'_168 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_zero'691'_184
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.zeroˡ
d_zero'737'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_zero'737'_170 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_zero'737'_170 v4 v5 v6 v7
du_zero'737'_170 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_zero'737'_170 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
                    (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_zero'737'_178
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMonoid_128 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMonoidMonomorphism_688
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.inverse
d_inverse_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_172 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_inverse_172 v4 v5 v6 v7
du_inverse_172 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_172 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.GroupMonomorphism.du_inverse_206
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
            (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.inverseʳ
d_inverse'691'_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_inverse'691'_174 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_inverse'691'_174 v4 v5 v6 v7
du_inverse'691'_174 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_inverse'691'_174 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.GroupMonomorphism.du_inverse'691'_200
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
            (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.inverseˡ
d_inverse'737'_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_inverse'737'_176 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_inverse'737'_176 v4 v5 v6 v7
du_inverse'737'_176 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_inverse'737'_176 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.GroupMonomorphism.du_inverse'737'_194
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
            (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.isAbelianGroup
d_isAbelianGroup_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130
d_isAbelianGroup_178 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isAbelianGroup_178 v4 v5 v6 v7
du_isAbelianGroup_178 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130
du_isAbelianGroup_178 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.GroupMonomorphism.du_isAbelianGroup_418
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
            (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.isGroup
d_isGroup_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
d_isGroup_180 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isGroup_180 v4 v5 v6 v7
du_isGroup_180 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
du_isGroup_180 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.GroupMonomorphism.du_isGroup_350
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
            (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.⁻¹-cong
d_'8315''185''45'cong_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_182 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'8315''185''45'cong_182 v4 v5 v6 v7
du_'8315''185''45'cong_182 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'cong_182 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.GroupMonomorphism.du_'8315''185''45'cong_212
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
            (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.⁻¹-distrib-∙
d_'8315''185''45'distrib'45''8729'_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'distrib'45''8729'_184 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'8315''185''45'distrib'45''8729'_184 v4 v5 v6 v7
du_'8315''185''45'distrib'45''8729'_184 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'distrib'45''8729'_184 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.GroupMonomorphism.du_'8315''185''45'distrib'45''8729'_342
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
            (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.assoc
d_assoc_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_188 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_assoc_188 v4 v5 v6 v7
du_assoc_188 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_188 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_assoc_160
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.cancel
d_cancel_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cancel_190 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cancel_190 v4 v5 v6 v7
du_cancel_190 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cancel_190 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel_236
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.cancelʳ
d_cancel'691'_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'691'_192 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cancel'691'_192 v4 v5 v6 v7
du_cancel'691'_192 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'691'_192 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel'691'_224
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.cancelˡ
d_cancel'737'_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'737'_194 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cancel'737'_194 v4 v5 v6 v7
du_cancel'737'_194 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'737'_194 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel'737'_212
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.comm
d_comm_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_196 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_comm_196 v4 v5 v6 v7
du_comm_196 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_196 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_comm_170
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.cong
d_cong_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_198 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_cong_198 v4 v5 v6 v7
du_cong_198 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cong_198 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cong_146
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.idem
d_idem_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_idem_200 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_idem_200 v4 v5 v6 v7
du_idem_200 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_idem_200 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_idem_178
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.identity
d_identity_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_202 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_identity_202 v4 v5 v6 v7
du_identity_202 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_202 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_identity_176
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.identityʳ
d_identity'691'_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_identity'691'_204 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_identity'691'_204 v4 v5 v6 v7
du_identity'691'_204 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_identity'691'_204 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_identity'691'_170
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.identityˡ
d_identity'737'_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_identity'737'_206 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_identity'737'_206 v4 v5 v6 v7
du_identity'737'_206 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_identity'737'_206 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_identity'737'_164
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.isBand
d_isBand_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506
d_isBand_208 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isBand_208 v4 v5 v6 v7
du_isBand_208 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506
du_isBand_208 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isBand_302
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.isCommutativeMonoid
d_isCommutativeMonoid_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_isCommutativeMonoid_210 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isCommutativeMonoid_210 v4 v5 v6 v7
du_isCommutativeMonoid_210 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_isCommutativeMonoid_210 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_isCommutativeMonoid_236
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.isMagma
d_isMagma_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_212 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isMagma_212 v4 v5 v6 v7
du_isMagma_212 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_212 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isMagma_238
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.isMonoid
d_isMonoid_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_214 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isMonoid_214 v4 v5 v6 v7
du_isMonoid_214 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_isMonoid_214 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_isMonoid_192
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.isSelectiveMagma
d_isSelectiveMagma_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434
d_isSelectiveMagma_216 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isSelectiveMagma_216 v4 v5 v6 v7
du_isSelectiveMagma_216 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434
du_isSelectiveMagma_216 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isSelectiveMagma_340
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.isSemigroup
d_isSemigroup_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_218 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isSemigroup_218 v4 v5 v6 v7
du_isSemigroup_218 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_218 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isSemigroup_268
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.sel
d_sel_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_220 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_sel_220 v4 v5 v6 v7
du_sel_220 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sel_220 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
              (coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
                 (coe
                    MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
                    (coe v3) in
          coe
            (coe
               MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_sel_184
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v4))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v5))
               (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
                  (coe v6)))))
-- Algebra.Morphism.RingMonomorphism._.zero
d_zero_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_222 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_zero_222 v4 v5 v6 v7
du_zero_222 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_222 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_zero_190
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.zeroʳ
d_zero'691'_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_zero'691'_224 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_zero'691'_224 v4 v5 v6 v7
du_zero'691'_224 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_zero'691'_224 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_zero'691'_184
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.zeroˡ
d_zero'737'_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_zero'737'_226 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_zero'737'_226 v4 v5 v6 v7
du_zero'737'_226 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_zero'737'_226 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_zero'737'_178
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
         (coe v3))
-- Algebra.Morphism.RingMonomorphism._.distribˡ
d_distrib'737'_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_352 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                   v13
  = du_distrib'737'_352 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_distrib'737'_352 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_352 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_2426 v3
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7
         (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0 v8 v9))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
         (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)
         (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v9))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v10 v11 v12 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v12)
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0 v8 v9)))
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v9)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0 v8 v9)))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
               (coe
                  v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0 v8 v9)))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v9)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0 v8 v9)))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v1 (coe v2 v8)
                     (coe v2 v9)))
               (coe
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
                     (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)
                     (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v9)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v1 (coe v2 v8)
                        (coe v2 v9)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v1
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                        (coe v2 v8))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                        (coe v2 v9)))
                  (coe
                     v2
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v9)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
                     (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5)))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v1
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                           (coe v2 v8))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                           (coe v2 v9)))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v1
                        (coe
                           v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8))
                        (coe
                           v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v9)))
                     (coe
                        v2
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
                           (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)
                           (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v9)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
                        (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                           (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5)))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v1
                           (coe
                              v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8))
                           (coe
                              v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v9)))
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v9)))
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v9)))
                        (let v10
                               = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                      (coe v5)) in
                         coe
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                 (coe v10))
                              (coe
                                 v2
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
                                    (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)
                                    (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v9)))))
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                           (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_370
                              (coe
                                 MAlonzo.Code.Algebra.Morphism.Structures.d_'43''45'isMonoidHomomorphism_936
                                 (coe
                                    MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                                    (coe
                                       MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                                       (coe
                                          MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                          (coe v3))))))
                           (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)
                           (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v9)))
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                        (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                              (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4))))
                        (coe
                           v2
                           (let v10
                                  = coe
                                      MAlonzo.Code.Algebra.Bundles.Raw.du_rawNearSemiring_210
                                      (coe
                                         MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
                                         (coe v0)) in
                            coe (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__162 v10 v7 v8)))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                           (coe v2 v8))
                        (coe
                           v2
                           (let v10
                                  = coe
                                      MAlonzo.Code.Algebra.Bundles.Raw.du_rawNearSemiring_210
                                      (coe
                                         MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
                                         (coe v0)) in
                            coe (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__162 v10 v7 v9)))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                           (coe v2 v9))
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_'42''45'homo_938
                           (MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                              (coe
                                 MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                                 (coe
                                    MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                    (coe v3))))
                           v7 v8)
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_'42''45'homo_938
                           (MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                              (coe
                                 MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                                 (coe
                                    MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                    (coe v3))))
                           v7 v9)))
                  (coe v6 (coe v2 v7) (coe v2 v8) (coe v2 v9)))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 v5 (coe v2 v7)
                  (coe v2 v7)
                  (coe
                     v2
                     (let v10
                            = coe
                                MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92
                                (coe
                                   MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawMonoid_166
                                   (coe
                                      MAlonzo.Code.Algebra.Bundles.Raw.du_rawNearSemiring_210
                                      (coe
                                         MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
                                         (coe v0)))) in
                      coe
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v10 v8 v9)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v1 (coe v2 v8)
                     (coe v2 v9))
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                     (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))
                     (coe v2 v7))
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_370
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_'43''45'isMonoidHomomorphism_936
                           (coe
                              MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                              (coe
                                 MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                                 (coe
                                    MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                    (coe v3))))))
                     v8 v9)))
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.d_'42''45'homo_938
               (MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                     (coe
                        MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                        (coe v3))))
               v7 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0 v8 v9))))
-- Algebra.Morphism.RingMonomorphism._.distribʳ
d_distrib'691'_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_362 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
                   v13
  = du_distrib'691'_362 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_distrib'691'_362 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_362 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_2426 v3
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
         (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0 v8 v9) v7)
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
         (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v8 v7)
         (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v9 v7))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v10 v11 v12 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v12)
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0 v8 v9) v7))
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v8 v7)
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v9 v7)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0 v8 v9) v7))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1
               (coe
                  v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0 v8 v9))
               (coe v2 v7))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v8 v7)
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v9 v7)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0 v8 v9))
                  (coe v2 v7))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v1 (coe v2 v8)
                     (coe v2 v9))
                  (coe v2 v7))
               (coe
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
                     (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v8 v7)
                     (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v9 v7)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v1 (coe v2 v8)
                        (coe v2 v9))
                     (coe v2 v7))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v1
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v8)
                        (coe v2 v7))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v9)
                        (coe v2 v7)))
                  (coe
                     v2
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v8 v7)
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v9 v7)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
                     (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5)))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v1
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v8)
                           (coe v2 v7))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v9)
                           (coe v2 v7)))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v1
                        (coe
                           v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v8 v7))
                        (coe
                           v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v9 v7)))
                     (coe
                        v2
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
                           (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v8 v7)
                           (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v9 v7)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
                        (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                           (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5)))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v1
                           (coe
                              v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v8 v7))
                           (coe
                              v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v9 v7)))
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v8 v7)
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v9 v7)))
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v8 v7)
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v9 v7)))
                        (let v10
                               = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                      (coe v5)) in
                         coe
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                 (coe v10))
                              (coe
                                 v2
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0
                                    (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v8 v7)
                                    (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v9 v7)))))
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                           (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_370
                              (coe
                                 MAlonzo.Code.Algebra.Morphism.Structures.d_'43''45'isMonoidHomomorphism_936
                                 (coe
                                    MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                                    (coe
                                       MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                                       (coe
                                          MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                          (coe v3))))))
                           (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v8 v7)
                           (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v9 v7)))
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                        (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                              (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4))))
                        (coe
                           v2
                           (let v10
                                  = coe
                                      MAlonzo.Code.Algebra.Bundles.Raw.du_rawNearSemiring_210
                                      (coe
                                         MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
                                         (coe v0)) in
                            coe (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__162 v10 v8 v7)))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v8)
                           (coe v2 v7))
                        (coe
                           v2
                           (let v10
                                  = coe
                                      MAlonzo.Code.Algebra.Bundles.Raw.du_rawNearSemiring_210
                                      (coe
                                         MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
                                         (coe v0)) in
                            coe (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__162 v10 v9 v7)))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v9)
                           (coe v2 v7))
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_'42''45'homo_938
                           (MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                              (coe
                                 MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                                 (coe
                                    MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                    (coe v3))))
                           v8 v7)
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_'42''45'homo_938
                           (MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                              (coe
                                 MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                                 (coe
                                    MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                    (coe v3))))
                           v9 v7)))
                  (coe v6 (coe v2 v7) (coe v2 v8) (coe v2 v9)))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 v5
                  (coe
                     v2
                     (let v10
                            = coe
                                MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92
                                (coe
                                   MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawMonoid_166
                                   (coe
                                      MAlonzo.Code.Algebra.Bundles.Raw.du_rawNearSemiring_210
                                      (coe
                                         MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
                                         (coe v0)))) in
                      coe
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v10 v8 v9)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v1 (coe v2 v8)
                     (coe v2 v9))
                  (coe v2 v7) (coe v2 v7)
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_370
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_'43''45'isMonoidHomomorphism_936
                           (coe
                              MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                              (coe
                                 MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                                 (coe
                                    MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                    (coe v3))))))
                     v8 v9)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                     (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))
                     (coe v2 v7))))
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.d_'42''45'homo_938
               (MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                     (coe
                        MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                        (coe v3))))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 v0 v8 v9) v7)))
-- Algebra.Morphism.RingMonomorphism._.distrib
d_distrib_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_372 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_distrib_372 v4 v5 v6 v7 v8 v9 v10
du_distrib_372 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_distrib_372 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_distrib'737'_352 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
      (coe
         du_distrib'691'_362 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6)))
-- Algebra.Morphism.RingMonomorphism._.zeroˡ
d_zero'737'_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_zero'737'_376 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10 v11
  = du_zero'737'_376 v4 v5 v6 v7 v9 v10 v11
du_zero'737'_376 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_zero'737'_376 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_2426 v3
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
         (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)) v6)
      (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v9)
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
               (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)) v6))
         (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)) v6))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1
               (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
               (coe v2 v6))
            (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
                  (coe v2 v6))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1))
                  (coe v2 v6))
               (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1
                     (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1))
                     (coe v2 v6))
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1))
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                     (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4)))
                     (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1))
                     (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
                     (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
                     (let v7
                            = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4)) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe v7))
                           (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))))
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_ε'45'homo_372
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_'43''45'isMonoidHomomorphism_936
                           (coe
                              MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                              (coe
                                 MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                                 (coe
                                    MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                    (coe v3)))))))
                  (coe v5 (coe v2 v6)))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 v4
                  (coe
                     v2
                     (let v7
                            = coe
                                MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawMonoid_166
                                (coe
                                   MAlonzo.Code.Algebra.Bundles.Raw.du_rawNearSemiring_210
                                   (coe
                                      MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
                                      (coe v0))) in
                      coe (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v7))))
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1)) (coe v2 v6)
                  (coe v2 v6)
                  (MAlonzo.Code.Algebra.Morphism.Structures.d_ε'45'homo_372
                     (coe
                        MAlonzo.Code.Algebra.Morphism.Structures.d_'43''45'isMonoidHomomorphism_936
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                           (coe
                              MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                              (coe
                                 MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                 (coe v3))))))
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                     (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))
                     (coe v2 v6))))
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.d_'42''45'homo_938
               (MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                     (coe
                        MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                        (coe v3))))
               (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)) v6)))
-- Algebra.Morphism.RingMonomorphism._.zeroʳ
d_zero'691'_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_zero'691'_382 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10 v11
  = du_zero'691'_382 v4 v5 v6 v7 v9 v10 v11
du_zero'691'_382 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_zero'691'_382 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_2426 v3
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v6
         (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
      (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v9)
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v6
               (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0))))
         (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v6
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0))))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v6)
               (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0))))
            (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v6)
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v6)
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1)))
               (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v6)
                     (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1)))
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1))
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                     (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4)))
                     (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1))
                     (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
                     (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))
                     (let v7
                            = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4)) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe v7))
                           (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))))
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_ε'45'homo_372
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_'43''45'isMonoidHomomorphism_936
                           (coe
                              MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                              (coe
                                 MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                                 (coe
                                    MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                    (coe v3)))))))
                  (coe v5 (coe v2 v6)))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 v4 (coe v2 v6)
                  (coe v2 v6)
                  (coe
                     v2
                     (let v7
                            = coe
                                MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawMonoid_166
                                (coe
                                   MAlonzo.Code.Algebra.Bundles.Raw.du_rawNearSemiring_210
                                   (coe
                                      MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
                                      (coe v0))) in
                      coe (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v7))))
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                     (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))
                     (coe v2 v6))
                  (MAlonzo.Code.Algebra.Morphism.Structures.d_ε'45'homo_372
                     (coe
                        MAlonzo.Code.Algebra.Morphism.Structures.d_'43''45'isMonoidHomomorphism_936
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                           (coe
                              MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                              (coe
                                 MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                 (coe v3))))))))
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.d_'42''45'homo_938
               (MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                     (coe
                        MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                        (coe v3))))
               v6 (MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v0)))))
-- Algebra.Morphism.RingMonomorphism._.zero
d_zero_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_388 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 ~v8 v9 v10
  = du_zero_388 v4 v5 v6 v7 v9 v10
du_zero_388 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_388 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_zero'737'_376 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
      (coe
         du_zero'691'_382 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
-- Algebra.Morphism.RingMonomorphism._.neg-distribˡ-*
d_neg'45'distrib'737''45''42'_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_neg'45'distrib'737''45''42'_400 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
                                  v10 v11 v12
  = du_neg'45'distrib'737''45''42'_400 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_neg'45'distrib'737''45''42'_400 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_neg'45'distrib'737''45''42'_400 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_2426 v3
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0
         (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
         (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7) v8)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v9 v10 v11 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v11)
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)))
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7) v8))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1
               (coe
                  v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7) v8))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                     (coe v2 v8)))
               (coe
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
                     (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7) v8))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                        (coe v2 v8)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1
                     (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1 (coe v2 v7))
                     (coe v2 v8))
                  (coe
                     v2
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7) v8))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1 (coe v2 v7))
                        (coe v2 v8))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1
                        (coe v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7))
                        (coe v2 v8))
                     (coe
                        v2
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
                           (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7) v8))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1
                           (coe v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7))
                           (coe v2 v8))
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7) v8))
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7) v8))
                        (let v9
                               = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                      (coe v5)) in
                         coe
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                 (coe v9))
                              (coe
                                 v2
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0
                                    (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7) v8))))
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                           (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))
                           (coe
                              v2
                              (let v9
                                     = coe
                                         MAlonzo.Code.Algebra.Bundles.Raw.du_rawNearSemiring_210
                                         (coe
                                            MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
                                            (coe v0)) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__162 v9
                                    (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7) v8)))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1
                              (coe v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7))
                              (coe v2 v8))
                           (coe
                              MAlonzo.Code.Algebra.Morphism.Structures.d_'42''45'homo_938
                              (MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                                 (coe
                                    MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                                    (coe
                                       MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                       (coe v3))))
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7) v8)))
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 v5
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1 (coe v2 v7))
                        (coe v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7))
                        (coe v2 v8) (coe v2 v8)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                           (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))
                           (coe v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v7))
                           (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1 (coe v2 v7))
                           (coe
                              MAlonzo.Code.Algebra.Morphism.Structures.d_'45''8255'homo_2384
                              (MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                 (coe v3))
                              v7))
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                           (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))
                           (coe v2 v8))))
                  (coe v6 (coe v2 v7) (coe v2 v8)))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1052 v4
                  (coe
                     v2
                     (let v9
                            = coe
                                MAlonzo.Code.Algebra.Bundles.Raw.du_rawNearSemiring_210
                                (coe
                                   MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)) in
                      coe (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__162 v9 v7 v8)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                     (coe v2 v8))
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_'42''45'homo_938
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                           (coe
                              MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                              (coe v3))))
                     v7 v8)))
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.d_'45''8255'homo_2384
               (MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                  (coe v3))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8))))
-- Algebra.Morphism.RingMonomorphism._.neg-distribʳ-*
d_neg'45'distrib'691''45''42'_416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_neg'45'distrib'691''45''42'_416 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
                                  v10 v11 v12
  = du_neg'45'distrib'691''45''42'_416 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_neg'45'distrib'691''45''42'_416 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_neg'45'distrib'691''45''42'_416 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_2426 v3
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0
         (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8))
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7
         (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v9 v10 v11 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v11)
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)))
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1
               (coe
                  v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8)))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                     (coe v2 v8)))
               (coe
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7
                     (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                        (coe v2 v8)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                     (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1 (coe v2 v8)))
                  (coe
                     v2
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1 (coe v2 v8)))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                        (coe v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8)))
                     (coe
                        v2
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7
                           (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                           (coe v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8)))
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8)))
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8)))
                        (let v9
                               = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                      (coe v5)) in
                         coe
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                 (coe v9))
                              (coe
                                 v2
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7
                                    (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8)))))
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                           (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))
                           (coe
                              v2
                              (let v9
                                     = coe
                                         MAlonzo.Code.Algebra.Bundles.Raw.du_rawNearSemiring_210
                                         (coe
                                            MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310
                                            (coe v0)) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__162 v9 v7
                                    (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8))))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                              (coe v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8)))
                           (coe
                              MAlonzo.Code.Algebra.Morphism.Structures.d_'42''45'homo_938
                              (MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                                 (coe
                                    MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                                    (coe
                                       MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                       (coe v3))))
                              v7 (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8))))
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 v5 (coe v2 v7)
                        (coe v2 v7)
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1 (coe v2 v8))
                        (coe v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8))
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                           (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))
                           (coe v2 v7))
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                           (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))
                           (coe v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v0 v8))
                           (coe MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 v1 (coe v2 v8))
                           (coe
                              MAlonzo.Code.Algebra.Morphism.Structures.d_'45''8255'homo_2384
                              (MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                                 (coe v3))
                              v8))))
                  (coe v6 (coe v2 v7) (coe v2 v8)))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1052 v4
                  (coe
                     v2
                     (let v9
                            = coe
                                MAlonzo.Code.Algebra.Bundles.Raw.du_rawNearSemiring_210
                                (coe
                                   MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)) in
                      coe (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__162 v9 v7 v8)))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v1 (coe v2 v7)
                     (coe v2 v8))
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_'42''45'homo_938
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_isNearSemiringHomomorphism_1302
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_isSemiringHomomorphism_2382
                           (coe
                              MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                              (coe v3))))
                     v7 v8)))
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.d_'45''8255'homo_2384
               (MAlonzo.Code.Algebra.Morphism.Structures.d_isRingHomomorphism_2424
                  (coe v3))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 v0 v7 v8))))
-- Algebra.Morphism.RingMonomorphism.isRing
d_isRing_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670
d_isRing_424 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_isRing_424 v4 v5 v6 v7 v8
du_isRing_424 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670
du_isRing_424 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsRing'46'constructor_96155
      (coe
         MAlonzo.Code.Algebra.Morphism.GroupMonomorphism.du_isAbelianGroup_418
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
               (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_'43''45'rawGroup_270
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.du_rawRingWithoutOne_324
               (coe v1)))
         (coe v2)
         (coe
            MAlonzo.Code.Algebra.Morphism.Structures.du_'43''45'isGroupMonomorphism_2462
            (coe v3))
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
            (coe v4)))
      (coe
         MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cong_146
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0))))
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1))))
         (coe v2)
         (coe
            MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
               (coe v3)))
         (let v5 = MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 (coe v1) in
          coe
            (let v6 = MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 (coe v1) in
             coe
               (let v7 = MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 (coe v1) in
                coe
                  (let v8 = MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1) in
                   coe
                     (let v9
                            = coe
                                MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v5)
                              (coe v6) (coe v7) (coe v8) (coe v9)))))))))
      (coe
         MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_assoc_160
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0))))
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1))))
         (coe v2)
         (coe
            MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
               (coe v3)))
         (let v5 = MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 (coe v1) in
          coe
            (let v6 = MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 (coe v1) in
             coe
               (let v7 = MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 (coe v1) in
                coe
                  (let v8 = MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1) in
                   coe
                     (let v9
                            = coe
                                MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v5)
                              (coe v6) (coe v7) (coe v8) (coe v9))))))))
         (coe
            MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_2696 (coe v4)))
      (coe
         MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism.du_identity_176
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
            (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0)))
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
            (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1)))
         v2
         (coe
            MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
            (coe v3))
         (let v5 = MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 (coe v1) in
          coe
            (let v6 = MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 (coe v1) in
             coe
               (let v7 = MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 (coe v1) in
                coe
                  (let v8 = MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1) in
                   coe
                     (let v9
                            = coe
                                MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v5)
                              (coe v6) (coe v7) (coe v8) (coe v9))))))))
         (MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2698 (coe v4)))
      (coe
         du_distrib_372 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1142
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
               (coe v4)))
         (let v5 = MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 (coe v1) in
          coe
            (let v6 = MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 (coe v1) in
             coe
               (let v7 = MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 (coe v1) in
                coe
                  (let v8 = MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1) in
                   coe
                     (let v9
                            = coe
                                MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v5)
                              (coe v6) (coe v7) (coe v8) (coe v9))))))))
         (coe MAlonzo.Code.Algebra.Structures.d_distrib_2700 (coe v4)))
-- Algebra.Morphism.RingMonomorphism.isCommutativeRing
d_isCommutativeRing_542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816
d_isCommutativeRing_542 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_isCommutativeRing_542 v4 v5 v6 v7 v8
du_isCommutativeRing_542 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawRing_276 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsRingMonomorphism_2416 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816
du_isCommutativeRing_542 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeRing'46'constructor_102067
      (coe
         du_isRing_424 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4)))
      (coe
         MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_comm_170
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v0))))
         (coe
            MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.du_'42''45'rawMonoid_222
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.du_rawSemiring_310 (coe v1))))
         (coe v2)
         (coe
            MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.du_'42''45'isMonoidMonomorphism_2472
               (coe v3)))
         (let v5 = MAlonzo.Code.Algebra.Bundles.Raw.d__'43'__300 (coe v1) in
          coe
            (let v6 = MAlonzo.Code.Algebra.Bundles.Raw.d__'42'__302 (coe v1) in
             coe
               (let v7 = MAlonzo.Code.Algebra.Bundles.Raw.d_'45'__304 (coe v1) in
                coe
                  (let v8 = MAlonzo.Code.Algebra.Bundles.Raw.d_0'35'_306 (coe v1) in
                   coe
                     (let v9 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
                      coe
                        (let v10
                               = coe
                                   MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                                   (coe v9) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v5)
                                 (coe v6) (coe v7) (coe v8) (coe v10)))))))))
         (coe MAlonzo.Code.Algebra.Structures.d_'42''45'comm_2834 (coe v4)))
