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

module MAlonzo.Code.Algebra.Morphism.MonoidMonomorphism where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism
import qualified MAlonzo.Code.Algebra.Morphism.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Morphism.MonoidMonomorphism._._∙_
d__'8729'__44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__44 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 = du__'8729'__44 v4
du__'8729'__44 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8729'__44 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 (coe v0)
-- Algebra.Morphism.MonoidMonomorphism._._≈_
d__'8776'__46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__46 = erased
-- Algebra.Morphism.MonoidMonomorphism._.ε
d_ε_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  AgdaAny
d_ε_54 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 = du_ε_54 v4
du_ε_54 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 -> AgdaAny
du_ε_54 v0 = coe MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)
-- Algebra.Morphism.MonoidMonomorphism._._≈_
d__'8776'__58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__58 = erased
-- Algebra.Morphism.MonoidMonomorphism._._∙_
d__'8729'__62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__62 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du__'8729'__62 v5
du__'8729'__62 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8729'__62 v0
  = coe MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 (coe v0)
-- Algebra.Morphism.MonoidMonomorphism._.ε
d_ε_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  AgdaAny
d_ε_68 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du_ε_68 v5
du_ε_68 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 -> AgdaAny
du_ε_68 v0 = coe MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)
-- Algebra.Morphism.MonoidMonomorphism._.assoc
d_assoc_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_72 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_assoc_72 v4 v5 v6 v7
du_assoc_72 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_72 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_assoc_160
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
         (coe v3))
-- Algebra.Morphism.MonoidMonomorphism._.cancel
d_cancel_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cancel_74 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_cancel_74 v4 v5 v6 v7
du_cancel_74 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cancel_74 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel_236
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
         (coe v3))
-- Algebra.Morphism.MonoidMonomorphism._.cancelʳ
d_cancel'691'_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'691'_76 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cancel'691'_76 v4 v5 v6 v7
du_cancel'691'_76 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'691'_76 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel'691'_224
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
         (coe v3))
-- Algebra.Morphism.MonoidMonomorphism._.cancelˡ
d_cancel'737'_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'737'_78 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cancel'737'_78 v4 v5 v6 v7
du_cancel'737'_78 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'737'_78 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel'737'_212
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
         (coe v3))
-- Algebra.Morphism.MonoidMonomorphism._.comm
d_comm_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_80 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_comm_80 v4 v5 v6 v7
du_comm_80 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_80 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_comm_170
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
         (coe v3))
-- Algebra.Morphism.MonoidMonomorphism._.cong
d_cong_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_82 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_cong_82 v4 v5 v6 v7
du_cong_82 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cong_82 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cong_146
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
         (coe v3))
-- Algebra.Morphism.MonoidMonomorphism._.idem
d_idem_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_idem_84 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_idem_84 v4 v5 v6 v7
du_idem_84 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_idem_84 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_idem_178
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
         (coe v3))
-- Algebra.Morphism.MonoidMonomorphism._.isBand
d_isBand_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506
d_isBand_86 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_isBand_86 v4 v5 v6 v7
du_isBand_86 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506
du_isBand_86 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isBand_302
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
         (coe v3))
-- Algebra.Morphism.MonoidMonomorphism._.isMagma
d_isMagma_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_88 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isMagma_88 v4 v5 v6 v7
du_isMagma_88 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_88 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isMagma_238
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
         (coe v3))
-- Algebra.Morphism.MonoidMonomorphism._.isSelectiveMagma
d_isSelectiveMagma_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434
d_isSelectiveMagma_90 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isSelectiveMagma_90 v4 v5 v6 v7
du_isSelectiveMagma_90 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434
du_isSelectiveMagma_90 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isSelectiveMagma_340
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
         (coe v3))
-- Algebra.Morphism.MonoidMonomorphism._.isSemigroup
d_isSemigroup_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_92 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_isSemigroup_92 v4 v5 v6 v7
du_isSemigroup_92 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_92 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isSemigroup_268
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
         (coe v3))
-- Algebra.Morphism.MonoidMonomorphism._.sel
d_sel_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_94 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_sel_94 v4 v5 v6 v7
du_sel_94 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sel_94 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_sel_184
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
      (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
         (coe v3))
-- Algebra.Morphism.MonoidMonomorphism._.identityˡ
d_identity'737'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_identity'737'_164 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_identity'737'_164 v4 v5 v6 v7 v8 v9 v10
du_identity'737'_164 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_identity'737'_164 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_394 v3
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v0
         (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)) v6)
      v6
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v9)
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v0
               (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)) v6))
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
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v0
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)) v6))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1
               (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
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
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
                  (coe v2 v6))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1)) (coe v2 v6))
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
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1
                     (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1)) (coe v2 v6))
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
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 v4
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1)) (coe v2 v6)
                  (coe v2 v6)
                  (MAlonzo.Code.Algebra.Morphism.Structures.d_ε'45'homo_372
                     (coe
                        MAlonzo.Code.Algebra.Morphism.Structures.d_isMonoidHomomorphism_392
                        (coe v3)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                     (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))
                     (coe v2 v6))))
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
               (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_370
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_isMonoidHomomorphism_392
                     (coe v3)))
               (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)) v6)))
-- Algebra.Morphism.MonoidMonomorphism._.identityʳ
d_identity'691'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_identity'691'_170 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_identity'691'_170 v4 v5 v6 v7 v8 v9 v10
du_identity'691'_170 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_identity'691'_170 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_394 v3
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v0 v6
         (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
      v6
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v9)
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v0 v6
               (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0))))
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
               v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v0 v6
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0))))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1 (coe v2 v6)
               (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0))))
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
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1 (coe v2 v6)
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1 (coe v2 v6)
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1)))
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
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1 (coe v2 v6)
                     (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1)))
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
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 v4 (coe v2 v6)
                  (coe v2 v6)
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                     (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))
                     (coe v2 v6))
                  (MAlonzo.Code.Algebra.Morphism.Structures.d_ε'45'homo_372
                     (coe
                        MAlonzo.Code.Algebra.Morphism.Structures.d_isMonoidHomomorphism_392
                        (coe v3)))))
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
               (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_370
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_isMonoidHomomorphism_392
                     (coe v3)))
               v6 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))))
-- Algebra.Morphism.MonoidMonomorphism._.identity
d_identity_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_176 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_identity_176 v4 v5 v6 v7 v8
du_identity_176 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_176 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe
         du_identity'737'_164 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
      (coe
         (\ v5 ->
            coe
              du_identity'691'_170 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)))
-- Algebra.Morphism.MonoidMonomorphism._.zeroˡ
d_zero'737'_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_zero'737'_178 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_zero'737'_178 v4 v5 v6 v7 v8 v9 v10
du_zero'737'_178 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_zero'737'_178 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_394 v3
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v0
         (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)) v6)
      (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v9)
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v0
               (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)) v6))
         (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
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
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v0
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)) v6))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1
               (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
               (coe v2 v6))
            (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
                  (coe v2 v6))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1)) (coe v2 v6))
               (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1
                     (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1)) (coe v2 v6))
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1))
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
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
                     (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1))
                     (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
                     (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
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
                           (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))))
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_ε'45'homo_372
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_isMonoidHomomorphism_392
                           (coe v3))))
                  (coe v5 (coe v2 v6)))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 v4
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1)) (coe v2 v6)
                  (coe v2 v6)
                  (MAlonzo.Code.Algebra.Morphism.Structures.d_ε'45'homo_372
                     (coe
                        MAlonzo.Code.Algebra.Morphism.Structures.d_isMonoidHomomorphism_392
                        (coe v3)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                     (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))
                     (coe v2 v6))))
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
               (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_370
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_isMonoidHomomorphism_392
                     (coe v3)))
               (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)) v6)))
-- Algebra.Morphism.MonoidMonomorphism._.zeroʳ
d_zero'691'_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_zero'691'_184 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10
  = du_zero'691'_184 v4 v5 v6 v7 v8 v9 v10
du_zero'691'_184 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_zero'691'_184 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Morphism.Structures.d_injective_394 v3
      (coe
         MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v0 v6
         (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
      (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v9)
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v0 v6
               (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0))))
         (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
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
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v0 v6
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0))))
            (coe
               MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1 (coe v2 v6)
               (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0))))
            (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1 (coe v2 v6)
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1 (coe v2 v6)
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1)))
               (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.Raw.d__'8729'__88 v1 (coe v2 v6)
                     (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1)))
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1))
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
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
                     (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1))
                     (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
                     (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
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
                           (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))))
                     (MAlonzo.Code.Algebra.Morphism.Structures.d_ε'45'homo_372
                        (coe
                           MAlonzo.Code.Algebra.Morphism.Structures.d_isMonoidHomomorphism_392
                           (coe v3))))
                  (coe v5 (coe v2 v6)))
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 v4 (coe v2 v6)
                  (coe v2 v6)
                  (coe v2 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))
                  (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v1))
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                     (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))
                     (coe v2 v6))
                  (MAlonzo.Code.Algebra.Morphism.Structures.d_ε'45'homo_372
                     (coe
                        MAlonzo.Code.Algebra.Morphism.Structures.d_isMonoidHomomorphism_392
                        (coe v3)))))
            (coe
               MAlonzo.Code.Algebra.Morphism.Structures.d_homo_198
               (MAlonzo.Code.Algebra.Morphism.Structures.d_isMagmaHomomorphism_370
                  (coe
                     MAlonzo.Code.Algebra.Morphism.Structures.d_isMonoidHomomorphism_392
                     (coe v3)))
               v6 (MAlonzo.Code.Algebra.Bundles.Raw.d_ε_90 (coe v0)))))
-- Algebra.Morphism.MonoidMonomorphism._.zero
d_zero_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_190 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_zero_190 v4 v5 v6 v7 v8
du_zero_190 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_190 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe du_zero'737'_178 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
      (coe
         (\ v5 ->
            coe du_zero'691'_184 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)))
-- Algebra.Morphism.MonoidMonomorphism.isMonoid
d_isMonoid_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_192 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_isMonoid_192 v4 v5 v6 v7 v8
du_isMonoid_192 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_isMonoid_192 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15345
      (coe
         MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_isSemigroup_268
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
         (coe v2)
         (coe
            MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
            (coe v3))
         (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v4)))
      (coe
         du_identity_176 v0 v1 v2 v3
         (MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v4)))
         (MAlonzo.Code.Algebra.Structures.d_identity_696 (coe v4)))
-- Algebra.Morphism.MonoidMonomorphism.isCommutativeMonoid
d_isCommutativeMonoid_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_isCommutativeMonoid_236 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_isCommutativeMonoid_236 v4 v5 v6 v7 v8
du_isCommutativeMonoid_236 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Morphism.Structures.T_IsMonoidMonomorphism_384 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_isCommutativeMonoid_236 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17167
      (coe
         du_isMonoid_192 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v4)))
      (coe
         MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_comm_170
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.Raw.du_rawMagma_92 (coe v1))
         (coe v2)
         (coe
            MAlonzo.Code.Algebra.Morphism.Structures.du_isMagmaMonomorphism_408
            (coe v3))
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v4))))
         (coe MAlonzo.Code.Algebra.Structures.d_comm_746 (coe v4)))
