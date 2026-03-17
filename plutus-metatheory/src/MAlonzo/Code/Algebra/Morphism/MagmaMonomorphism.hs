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

module MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Morphism.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Morphism.RelMonomorphism
import qualified MAlonzo.Code.Relation.Binary.Morphism.Structures
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Morphism.MagmaMonomorphism._._∙_
d__'8729'__38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__38 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 = du__'8729'__38 v4
du__'8729'__38 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8729'__38 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 (coe v0)
-- Algebra.Morphism.MagmaMonomorphism._._≈_
d__'8776'__40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__40 = erased
-- Algebra.Morphism.MagmaMonomorphism._._≈_
d__'8776'__50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__50 = erased
-- Algebra.Morphism.MagmaMonomorphism._._∙_
d__'8729'__54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__54 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du__'8729'__54 v5
du__'8729'__54 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8729'__54 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 (coe v0)
-- Algebra.Morphism.MagmaMonomorphism._.cong
d_cong_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_146 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
  = du_cong_146 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_cong_146 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cong_146 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_216 v3
      (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v5 v7)
      (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v8)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v11 v12 v13 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v13)
         (coe
            v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v5 v7))
         (coe
            v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v8))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
            (coe
               v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v5 v7))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v5)
               (coe v2 v7))
            (coe
               v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v8))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v5)
                  (coe v2 v7))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                  (coe v2 v8))
               (coe
                  v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v8))
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
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                     (coe v2 v8))
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v8))
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v8))
                  (let v11
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4)) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v11))
                        (coe
                           v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v8))))
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                        (coe v3))
                     v6 v8))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 v4 (coe v2 v5)
                  (coe v2 v6) (coe v2 v7) (coe v2 v8)
                  (coe
                     MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_isRelHomomorphism_196
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                           (coe v3)))
                     v5 v6 v9)
                  (coe
                     MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_isRelHomomorphism_196
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                           (coe v3)))
                     v7 v8 v10)))
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
               (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                  (coe v3))
               v5 v7)))
-- Algebra.Morphism.MagmaMonomorphism._.assoc
d_assoc_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_160 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = du_assoc_160 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_assoc_160 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_160 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_216 v3
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0
         (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7) v8)
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6
         (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v8))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v9 v10 v11 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v11)
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7) v8))
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v8)))
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
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7) v8))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1
               (coe
                  v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7))
               (coe v2 v8))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6
                  (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v8)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7))
                  (coe v2 v8))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                     (coe v2 v7))
                  (coe v2 v8))
               (coe
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6
                     (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v8)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                        (coe v2 v7))
                     (coe v2 v8))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v7)
                        (coe v2 v8)))
                  (coe
                     v2
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6
                        (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v8)))
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
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v7)
                           (coe v2 v8)))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                        (coe
                           v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v8)))
                     (coe
                        v2
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6
                           (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v8)))
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
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                           (coe
                              v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v8)))
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v8)))
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6
                              (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v8)))
                        (let v9
                               = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                      (coe v4)) in
                         coe
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                 (coe v9))
                              (coe
                                 v2
                                 (coe
                                    MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6
                                    (coe
                                       MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v8)))))
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                           (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                              (coe v3))
                           v6 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v8)))
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 v4 (coe v2 v6)
                        (coe v2 v6)
                        (coe
                           v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v8))
                        (coe
                           MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v7)
                           (coe v2 v8))
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                           (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))
                           (coe v2 v6))
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                           (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                              (coe v3))
                           v7 v8)))
                  (coe v5 (coe v2 v6) (coe v2 v7) (coe v2 v8)))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 v4
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                     (coe v2 v7))
                  (coe v2 v8) (coe v2 v8)
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                        (coe v3))
                     v6 v7)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                     (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))
                     (coe v2 v8))))
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
               (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                  (coe v3))
               (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7) v8)))
-- Algebra.Morphism.MagmaMonomorphism._.comm
d_comm_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_170 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_comm_170 v4 v5 v6 v7 v8 v9 v10 v11
du_comm_170 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_170 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_216 v3
      (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7)
      (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v6)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v8 v9 v10 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v10)
         (coe
            v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7))
         (coe
            v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v6))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
            (coe
               v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
               (coe v2 v7))
            (coe
               v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v6))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                  (coe v2 v7))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v7)
                  (coe v2 v6))
               (coe
                  v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v6))
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
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v7)
                     (coe v2 v6))
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v6))
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v6))
                  (let v8
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4)) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v8))
                        (coe
                           v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v6))))
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                        (coe v3))
                     v7 v6))
               (coe v5 (coe v2 v6) (coe v2 v7)))
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
               (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                  (coe v3))
               v6 v7)))
-- Algebra.Morphism.MagmaMonomorphism._.idem
d_idem_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_idem_178 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_idem_178 v4 v5 v6 v7 v8 v9 v10
du_idem_178 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_idem_178 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_216 v3
      (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v6) v6
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v9)
         (coe
            v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v6))
         (coe v2 v6)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
            (coe
               v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v6))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
               (coe v2 v6))
            (coe v2 v6)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                  (coe v2 v6))
               (coe v2 v6) (coe v2 v6)
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
                     (coe v2 v6)))
               (coe v5 (coe v2 v6)))
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
               (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                  (coe v3))
               v6 v6)))
-- Algebra.Morphism.MagmaMonomorphism._.sel
d_sel_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_184 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_sel_184 v4 v5 v6 v7 v8 v9 v10 v11
du_sel_184 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sel_184 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8 = coe v5 (coe v2 v6) (coe v2 v7) in
    coe
      (case coe v8 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                (coe
                   MAlonzo.Code.Algebra.Morphism.Structures.d_injective_216 v3
                   (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7) v6
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                      (\ v10 v11 v12 ->
                         coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v12)
                      (coe
                         v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7))
                      (coe v2 v6)
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                         (coe
                            v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7))
                         (coe
                            MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                            (coe v2 v7))
                         (coe v2 v6)
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                               (coe
                                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                  (coe
                                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                            (coe
                               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                               (coe v2 v7))
                            (coe v2 v6) (coe v2 v6)
                            (let v10
                                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                          (coe v4)) in
                             coe
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                     (coe v10))
                                  (coe v2 v6)))
                            v9)
                         (coe
                            MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                            (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                               (coe v3))
                            v6 v7))))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                (coe
                   MAlonzo.Code.Algebra.Morphism.Structures.d_injective_216 v3
                   (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7) v7
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                      (\ v10 v11 v12 ->
                         coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v12)
                      (coe
                         v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7))
                      (coe v2 v7)
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                               (coe
                                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                         (coe
                            v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7))
                         (coe
                            MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                            (coe v2 v7))
                         (coe v2 v7)
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                               (coe
                                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                  (coe
                                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                            (coe
                               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                               (coe v2 v7))
                            (coe v2 v7) (coe v2 v7)
                            (let v10
                                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                          (coe v4)) in
                             coe
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                     (coe v10))
                                  (coe v2 v7)))
                            v9)
                         (coe
                            MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                            (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                               (coe v3))
                            v6 v7))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Morphism.MagmaMonomorphism._.cancelˡ
d_cancel'737'_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'737'_212 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_cancel'737'_212 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_cancel'737'_212 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'737'_212 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_216 v3 v7 v8
      (coe
         v5 (coe v2 v6) (coe v2 v7) (coe v2 v8)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (\ v10 v11 v12 ->
               coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v12)
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
               (coe v2 v7))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
               (coe v2 v8))
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
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                  (coe v2 v7))
               (coe
                  v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                  (coe v2 v8))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7))
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v8))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                     (coe v2 v8))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                     (coe
                        v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v8))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                        (coe v2 v8))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                        (coe v2 v8))
                     (let v10
                            = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4)) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe v10))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v6)
                              (coe v2 v8))))
                     (coe
                        MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                        (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                           (coe v3))
                        v6 v8))
                  (coe
                     MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_isRelHomomorphism_196
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                           (coe v3)))
                     (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v7)
                     (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v6 v8) v9))
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                  (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                     (coe v3))
                  v6 v7))))
-- Algebra.Morphism.MagmaMonomorphism._.cancelʳ
d_cancel'691'_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'691'_224 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  = du_cancel'691'_224 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
du_cancel'691'_224 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'691'_224 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_216 v3 v7 v8
      (coe
         v5 (coe v2 v6) (coe v2 v7) (coe v2 v8)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (\ v10 v11 v12 ->
               coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v12)
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v7)
               (coe v2 v6))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v8)
               (coe v2 v6))
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
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v7)
                  (coe v2 v6))
               (coe
                  v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v6))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v8)
                  (coe v2 v6))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v6))
                  (coe
                     v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v8 v6))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v8)
                     (coe v2 v6))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                     (coe
                        v2 (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v8 v6))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v8)
                        (coe v2 v6))
                     (coe
                        MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v8)
                        (coe v2 v6))
                     (let v10
                            = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                (coe
                                   MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4)) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe v10))
                           (coe
                              MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v1 (coe v2 v8)
                              (coe v2 v6))))
                     (coe
                        MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                        (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                           (coe v3))
                        v8 v6))
                  (coe
                     MAlonzo.Code.Relation.Binary.Morphism.Structures.d_cong_52
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_isRelHomomorphism_196
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                           (coe v3)))
                     (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v7 v6)
                     (coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__58 v0 v8 v6) v9))
               (coe
                  MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
                  (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_214
                     (coe v3))
                  v7 v6))))
-- Algebra.Morphism.MagmaMonomorphism._.cancel
d_cancel_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cancel_236 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_cancel_236 v4 v5 v6 v7 v8
du_cancel_236 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cancel_236 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe
         du_cancel'737'_212 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
      (coe
         (\ v5 ->
            coe
              du_cancel'691'_224 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)))
-- Algebra.Morphism.MagmaMonomorphism.isMagma
d_isMagma_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_238 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_isMagma_238 v4 v5 v6 v7 v8
du_isMagma_238 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_238 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe
         MAlonzo.Code.Relation.Binary.Morphism.RelMonomorphism.du_isEquivalence_78
         (coe v2)
         (coe
            MAlonzo.Code.Algebra.Morphism.Structures.du_isRelMonomorphism_226
            (coe v3))
         (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4)))
      (coe du_cong_146 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Algebra.Morphism.MagmaMonomorphism.isSemigroup
d_isSemigroup_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_268 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_isSemigroup_268 v4 v5 v6 v7 v8
du_isSemigroup_268 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_268 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_9889
      (coe
         du_isMagma_238 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v4)))
      (coe
         du_assoc_160 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v4))
         (coe MAlonzo.Code.Algebra.Structures.d_assoc_480 (coe v4)))
-- Algebra.Morphism.MagmaMonomorphism.isBand
d_isBand_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506
d_isBand_302 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_isBand_302 v4 v5 v6 v7 v8
du_isBand_302 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506
du_isBand_302 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsBand'46'constructor_10677
      (coe
         du_isSemigroup_268 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v4)))
      (coe
         du_idem_178 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v4)))
         (coe MAlonzo.Code.Algebra.Structures.d_idem_516 (coe v4)))
-- Algebra.Morphism.MagmaMonomorphism.isSelectiveMagma
d_isSelectiveMagma_340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434
d_isSelectiveMagma_340 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_isSelectiveMagma_340 v4 v5 v6 v7 v8
du_isSelectiveMagma_340 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMagmaMonomorphism_206 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434
du_isSelectiveMagma_340 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSelectiveMagma'46'constructor_9103
      (coe
         du_isMagma_238 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_442 (coe v4)))
      (coe
         du_sel_184 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Algebra.Structures.d_isMagma_442 (coe v4))
         (coe MAlonzo.Code.Algebra.Structures.d_sel_444 (coe v4)))
