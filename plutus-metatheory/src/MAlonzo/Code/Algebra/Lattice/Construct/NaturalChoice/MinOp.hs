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

module MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.Base qualified
import MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp qualified
import MAlonzo.Code.Algebra.Lattice.Bundles qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Lattice.Construct.NaturalChoice.MinOp._.IsSemilattice
d_IsSemilattice_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_IsSemilattice_114 = erased
-- Algebra.Lattice.Construct.NaturalChoice.MinOp.⊓-isSemilattice
d_'8851''45'isSemilattice_602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_'8851''45'isSemilattice_602 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isSemilattice_602 v3 v4
du_'8851''45'isSemilattice_602 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
du_'8851''45'isSemilattice_602 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeBand'46'constructor_13109
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3034
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2856
         (coe v0) (coe v1))
-- Algebra.Lattice.Construct.NaturalChoice.MinOp.⊓-semilattice
d_'8851''45'semilattice_604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_604 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'semilattice_604 v3 v4
du_'8851''45'semilattice_604 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_98 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
du_'8851''45'semilattice_604 v0 v1
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_Semilattice'46'constructor_193
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__114
         (coe v1))
      (coe du_'8851''45'isSemilattice_602 (coe v0) (coe v1))
