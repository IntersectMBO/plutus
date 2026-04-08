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

module MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MaxOp where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Base
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd

-- Algebra.Lattice.Construct.NaturalChoice.MaxOp.Min.⊓-isSemilattice
d_'8851''45'isSemilattice_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_'8851''45'isSemilattice_22 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isSemilattice_22 v3 v4
du_'8851''45'isSemilattice_22 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_'8851''45'isSemilattice_22 v0 v1
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_616
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Lattice.Construct.NaturalChoice.MaxOp.Min.⊓-semilattice
d_'8851''45'semilattice_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_24 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'semilattice_24 v3 v4
du_'8851''45'semilattice_24 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
du_'8851''45'semilattice_24 v0 v1
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_618
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
