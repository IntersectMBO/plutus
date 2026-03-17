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

module MAlonzo.Code.Algebra.Lattice.Morphism.LatticeMonomorphism where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Lattice.Morphism.Structures
import qualified MAlonzo.Code.Algebra.Lattice.Properties.Lattice
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Algebra.Lattice.Structures.Biased
import qualified MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism
import qualified MAlonzo.Code.Algebra.Morphism.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Morphism.RelMonomorphism
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Lattice.Morphism.LatticeMonomorphism._._∧_
d__'8743'__50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__50 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 = du__'8743'__50 v4
du__'8743'__50 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8743'__50 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 (coe v0)
-- Algebra.Lattice.Morphism.LatticeMonomorphism._._∨_
d__'8744'__52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__52 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 = du__'8744'__52 v4
du__'8744'__52 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8744'__52 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 (coe v0)
-- Algebra.Lattice.Morphism.LatticeMonomorphism._._≈_
d__'8776'__54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__54 = erased
-- Algebra.Lattice.Morphism.LatticeMonomorphism._._≈_
d__'8776'__66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__66 = erased
-- Algebra.Lattice.Morphism.LatticeMonomorphism._._∧_
d__'8743'__70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__70 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du__'8743'__70 v5
du__'8743'__70 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8743'__70 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 (coe v0)
-- Algebra.Lattice.Morphism.LatticeMonomorphism._._∨_
d__'8744'__72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__72 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 = du__'8744'__72 v5
du__'8744'__72 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8744'__72 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 (coe v0)
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.assoc
d_assoc_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_82 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_assoc_82 v4 v5 v6 v7
du_assoc_82 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_82 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_assoc_160
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8744''45'isMagmaMonomorphism_226
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.cancel
d_cancel_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cancel_84 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_cancel_84 v4 v5 v6 v7
du_cancel_84 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cancel_84 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel_236
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8744''45'isMagmaMonomorphism_226
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.cancelʳ
d_cancel'691'_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'691'_86 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cancel'691'_86 v4 v5 v6 v7
du_cancel'691'_86 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'691'_86 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel'691'_224
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8744''45'isMagmaMonomorphism_226
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.cancelˡ
d_cancel'737'_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'737'_88 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cancel'737'_88 v4 v5 v6 v7
du_cancel'737'_88 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'737'_88 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel'737'_212
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8744''45'isMagmaMonomorphism_226
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.comm
d_comm_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_90 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_comm_90 v4 v5 v6 v7
du_comm_90 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_90 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_comm_170
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8744''45'isMagmaMonomorphism_226
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.cong
d_cong_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_92 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_cong_92 v4 v5 v6 v7
du_cong_92 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cong_92 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cong_146
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8744''45'isMagmaMonomorphism_226
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.idem
d_idem_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_idem_94 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_idem_94 v4 v5 v6 v7
du_idem_94 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_idem_94 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_idem_178
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8744''45'isMagmaMonomorphism_226
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.sel
d_sel_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_96 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_sel_96 v4 v5 v6 v7
du_sel_96 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sel_96 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_sel_184
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8744''45'isMagmaMonomorphism_226
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.assoc
d_assoc_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_100 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_assoc_100 v4 v5 v6 v7
du_assoc_100 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_100 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_assoc_160
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8743''45'isMagmaMonomorphism_228
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.cancel
d_cancel_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cancel_102 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cancel_102 v4 v5 v6 v7
du_cancel_102 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cancel_102 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel_236
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8743''45'isMagmaMonomorphism_228
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.cancelʳ
d_cancel'691'_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'691'_104 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cancel'691'_104 v4 v5 v6 v7
du_cancel'691'_104 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'691'_104 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel'691'_224
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8743''45'isMagmaMonomorphism_228
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.cancelˡ
d_cancel'737'_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'737'_106 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_cancel'737'_106 v4 v5 v6 v7
du_cancel'737'_106 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'737'_106 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cancel'737'_212
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8743''45'isMagmaMonomorphism_228
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.comm
d_comm_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_108 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_comm_108 v4 v5 v6 v7
du_comm_108 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_108 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_comm_170
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8743''45'isMagmaMonomorphism_228
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.cong
d_cong_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_110 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_cong_110 v4 v5 v6 v7
du_cong_110 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cong_110 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cong_146
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8743''45'isMagmaMonomorphism_228
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.idem
d_idem_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_idem_112 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_idem_112 v4 v5 v6 v7
du_idem_112 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_idem_112 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_idem_178
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8743''45'isMagmaMonomorphism_228
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.sel
d_sel_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_114 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 = du_sel_114 v4 v5 v6 v7
du_sel_114 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sel_114 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_sel_184
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe v1))
      (coe v2)
      (coe
         MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8743''45'isMagmaMonomorphism_228
         (coe v3))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.setoid
d_setoid_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_setoid_138 v8
du_setoid_138 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_138 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_761
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
         (coe v0))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_180 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
                                  v10
  = du_'8744''45'absorbs'45''8743'_180 v4 v5 v6 v7 v8 v9 v10
du_'8744''45'absorbs'45''8743'_180 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_180 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_injective_210 v3
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v5
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v5 v6))
      v5
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v9)
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v5
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v5 v6)))
         (coe v2 v5)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                     (coe v4))))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v5
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v5 v6)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
               (coe v2 v5)
               (coe
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v5 v6)))
            (coe v2 v5)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                        (coe v4))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                  (coe v2 v5)
                  (coe
                     v2
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v5 v6)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                  (coe v2 v5)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v1
                     (coe v2 v5) (coe v2 v6)))
               (coe v2 v5)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                           (coe v4))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                     (coe v2 v5)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v1
                        (coe v2 v5) (coe v2 v6)))
                  (coe v2 v5) (coe v2 v5)
                  (let v7
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                                (coe v4)) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v7))
                        (coe v2 v5)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3034
                     v4 (coe v2 v5) (coe v2 v6)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3046
                  (coe v4) (coe v2 v5)
                  (coe
                     v2
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v5 v6))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v1
                     (coe v2 v5) (coe v2 v6))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_'8743''45'homo_186
                     (MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_isLatticeHomomorphism_208
                        (coe v3))
                     v5 v6)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_'8744''45'homo_188
               (MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_isLatticeHomomorphism_208
                  (coe v3))
               v5
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v5 v6))))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_186 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
                                  v10
  = du_'8743''45'absorbs'45''8744'_186 v4 v5 v6 v7 v8 v9 v10
du_'8743''45'absorbs'45''8744'_186 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_186 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_injective_210 v3
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v5
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v5 v6))
      v5
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v9)
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v5
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v5 v6)))
         (coe v2 v5)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                     (coe v4))))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v5
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v5 v6)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v1
               (coe v2 v5)
               (coe
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v5 v6)))
            (coe v2 v5)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                        (coe v4))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v1
                  (coe v2 v5)
                  (coe
                     v2
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v5 v6)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v1
                  (coe v2 v5)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                     (coe v2 v5) (coe v2 v6)))
               (coe v2 v5)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                           (coe v4))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v1
                     (coe v2 v5)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                        (coe v2 v5) (coe v2 v6)))
                  (coe v2 v5) (coe v2 v5)
                  (let v7
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                                (coe v4)) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v7))
                        (coe v2 v5)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3036
                     v4 (coe v2 v5) (coe v2 v6)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3038
                  (coe v4) (coe v2 v5)
                  (coe
                     v2
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v5 v6))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                     (coe v2 v5) (coe v2 v6))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_'8744''45'homo_188
                     (MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_isLatticeHomomorphism_208
                        (coe v3))
                     v5 v6)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_'8743''45'homo_186
               (MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_isLatticeHomomorphism_208
                  (coe v3))
               v5
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v5 v6))))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.absorptive
d_absorptive_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_192 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_absorptive_192 v4 v5 v6 v7 v8
du_absorptive_192 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_absorptive_192 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_'8744''45'absorbs'45''8743'_180 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4))
      (coe
         du_'8743''45'absorbs'45''8744'_186 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4))
-- Algebra.Lattice.Morphism.LatticeMonomorphism._.distribʳ
d_distrib'691'_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_194 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9 v10 v11 v12
  = du_distrib'691'_194 v4 v5 v6 v7 v8 v9 v10 v11 v12
du_distrib'691'_194 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_194 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_injective_210 v3
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v7 v8)
         v6)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v7 v6)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v8 v6))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v9 v10 v11 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v11)
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v7 v8)
               v6))
         (coe
            v2
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v7 v6)
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v8 v6)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                     (coe v4))))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v7 v8)
                  v6))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
               (coe
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v7 v8))
               (coe v2 v6))
            (coe
               v2
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v7 v6)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v8 v6)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                        (coe v4))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                  (coe
                     v2
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v7 v8))
                  (coe v2 v6))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v1
                     (coe v2 v7) (coe v2 v8))
                  (coe v2 v6))
               (coe
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v7 v6)
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v8 v6)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                           (coe v4))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v1
                        (coe v2 v7) (coe v2 v8))
                     (coe v2 v6))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v1
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                        (coe v2 v7) (coe v2 v6))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                        (coe v2 v8) (coe v2 v6)))
                  (coe
                     v2
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v7 v6)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v8 v6)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                              (coe v4))))
                     (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                           (coe v4)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v1
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                           (coe v2 v7) (coe v2 v6))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                           (coe v2 v8) (coe v2 v6)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v1
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v7 v6))
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v8 v6)))
                     (coe
                        v2
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v7 v6)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v8 v6)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                                 (coe v4))))
                        (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                              (coe v4)))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v1
                           (coe
                              v2
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v7 v6))
                           (coe
                              v2
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v8 v6)))
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v7 v6)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v8 v6)))
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v7 v6)
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v8 v6)))
                        (let v9
                               = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (coe
                                      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
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
                                    MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v7
                                       v6)
                                    (coe
                                       MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v8
                                       v6)))))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_'8743''45'homo_186
                           (MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_isLatticeHomomorphism_208
                              (coe v3))
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v7 v6)
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v8 v6)))
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3018 v4
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v7 v6))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                           (coe v2 v7) (coe v2 v6))
                        (coe
                           v2
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v0 v8 v6))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 v1
                           (coe v2 v8) (coe v2 v6))
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_'8744''45'homo_188
                           (MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_isLatticeHomomorphism_208
                              (coe v3))
                           v7 v6)
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_'8744''45'homo_188
                           (MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_isLatticeHomomorphism_208
                              (coe v3))
                           v8 v6)))
                  (coe v5 (coe v2 v6) (coe v2 v7) (coe v2 v8)))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3050
                  (coe v4) (coe v2 v6)
                  (coe
                     v2
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v7 v8))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v1
                     (coe v2 v7) (coe v2 v8))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_'8743''45'homo_186
                     (MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_isLatticeHomomorphism_208
                        (coe v3))
                     v7 v8)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_'8744''45'homo_188
               (MAlonzo.Code.Algebra.Lattice.Morphism.Structures.d_isLatticeHomomorphism_208
                  (coe v3))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 v0 v7 v8)
               v6)))
-- Algebra.Lattice.Morphism.LatticeMonomorphism.isLattice
d_isLattice_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
d_isLattice_204 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_isLattice_204 v4 v5 v6 v7 v8
du_isLattice_204 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
du_isLattice_204 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_IsLattice'46'constructor_36909
      (coe
         MAlonzo.Code.Relation.Binary.Morphism.RelMonomorphism.du_isEquivalence_78
         (coe v2)
         (coe
            MAlonzo.Code.Algebra.Morphism.Structures.du_isRelMonomorphism_226
            (coe
               MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8743''45'isMagmaMonomorphism_228
               (coe v3)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
            (coe v4)))
      (coe
         MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_comm_170
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
            (coe v1))
         (coe v2)
         (coe
            MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8744''45'isMagmaMonomorphism_226
            (coe v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isMagma_314
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.C_Lattice'46'constructor_7925
               (MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 (coe v1))
               (MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 (coe v1))
               v4))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3008
            (coe v4)))
      (coe
         MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_assoc_160
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
            (coe v1))
         (coe v2)
         (coe
            MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8744''45'isMagmaMonomorphism_226
            (coe v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isMagma_314
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.C_Lattice'46'constructor_7925
               (MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 (coe v1))
               (MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 (coe v1))
               v4))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3010
            (coe v4)))
      (coe
         MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cong_146
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
            (coe v1))
         (coe v2)
         (coe
            MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8744''45'isMagmaMonomorphism_226
            (coe v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isMagma_314
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.C_Lattice'46'constructor_7925
               (MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 (coe v1))
               (MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 (coe v1))
               v4)))
      (coe
         MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_comm_170
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
            (coe v1))
         (coe v2)
         (coe
            MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8743''45'isMagmaMonomorphism_228
            (coe v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isMagma_290
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.C_Lattice'46'constructor_7925
               (MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 (coe v1))
               (MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 (coe v1))
               v4))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3014
            (coe v4)))
      (coe
         MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_assoc_160
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
            (coe v1))
         (coe v2)
         (coe
            MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8743''45'isMagmaMonomorphism_228
            (coe v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isMagma_290
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.C_Lattice'46'constructor_7925
               (MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 (coe v1))
               (MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 (coe v1))
               v4))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3016
            (coe v4)))
      (coe
         MAlonzo.Code.Algebra.Morphism.MagmaMonomorphism.du_cong_146
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
            (coe v1))
         (coe v2)
         (coe
            MAlonzo.Code.Algebra.Lattice.Morphism.Structures.du_'8743''45'isMagmaMonomorphism_228
            (coe v3))
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isMagma_290
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.C_Lattice'46'constructor_7925
               (MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 (coe v1))
               (MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 (coe v1))
               v4)))
      (coe
         du_absorptive_192 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Algebra.Lattice.Morphism.LatticeMonomorphism.isDistributiveLattice
d_isDistributiveLattice_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
d_isDistributiveLattice_304 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_isDistributiveLattice_304 v4 v5 v6 v7 v8
du_isDistributiveLattice_304 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Morphism.Structures.T_IsLatticeMonomorphism_200 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
du_isDistributiveLattice_304 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.Biased.du_isDistributiveLattice'691''690''7504'_442
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8744'__32 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.d__'8743'__30 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.Biased.C_IsDistributiveLattice'691''690''7504''46'constructor_5653
         (coe
            du_isLattice_204 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v4)))
         (coe
            du_distrib'691'_194 (coe v0) (coe v1) (coe v2) (coe v3)
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v4))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3118
               (coe v4))))
