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

module MAlonzo.Code.Algebra.Lattice.Properties.Semilattice where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.NaturalOrder.Left
import qualified MAlonzo.Code.Relation.Binary.Lattice.Bundles
import qualified MAlonzo.Code.Relation.Binary.Lattice.Structures
import qualified MAlonzo.Code.Relation.Binary.Properties.Poset

-- Algebra.Lattice.Properties.Semilattice.poset
d_poset_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_162 ~v0 ~v1 v2 = du_poset_162 v2
du_poset_162 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_162 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NaturalOrder.Left.du_poset_3898
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8729'__28 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_isSemilattice_30 (coe v0))
-- Algebra.Lattice.Properties.Semilattice._._≤_
d__'8804'__166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  AgdaAny -> AgdaAny -> ()
d__'8804'__166 = erased
-- Algebra.Lattice.Properties.Semilattice._._∼ᵒ_
d__'8764''7506'__168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  AgdaAny -> AgdaAny -> ()
d__'8764''7506'__168 = erased
-- Algebra.Lattice.Properties.Semilattice.∧-isOrderTheoreticMeetSemilattice
d_'8743''45'isOrderTheoreticMeetSemilattice_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
d_'8743''45'isOrderTheoreticMeetSemilattice_176 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticMeetSemilattice_176 v2
du_'8743''45'isOrderTheoreticMeetSemilattice_176 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
du_'8743''45'isOrderTheoreticMeetSemilattice_176 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.C_constructor_274
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
         (coe du_poset_162 (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.NaturalOrder.Left.du_infimum_3754
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8729'__28 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isSemilattice_30 (coe v0)))
-- Algebra.Lattice.Properties.Semilattice.∧-isOrderTheoreticJoinSemilattice
d_'8743''45'isOrderTheoreticJoinSemilattice_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_'8743''45'isOrderTheoreticJoinSemilattice_178 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticJoinSemilattice_178 v2
du_'8743''45'isOrderTheoreticJoinSemilattice_178 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_'8743''45'isOrderTheoreticJoinSemilattice_178 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.C_constructor_112
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'isPartialOrder_150
         (coe du_poset_162 (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.NaturalOrder.Left.du_infimum_3754
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8729'__28 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isSemilattice_30 (coe v0)))
-- Algebra.Lattice.Properties.Semilattice.∧-orderTheoreticMeetSemilattice
d_'8743''45'orderTheoreticMeetSemilattice_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_204
d_'8743''45'orderTheoreticMeetSemilattice_180 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticMeetSemilattice_180 v2
du_'8743''45'orderTheoreticMeetSemilattice_180 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_204
du_'8743''45'orderTheoreticMeetSemilattice_180 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Bundles.C_constructor_286
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8729'__28 (coe v0))
      (coe du_'8743''45'isOrderTheoreticMeetSemilattice_176 (coe v0))
-- Algebra.Lattice.Properties.Semilattice.∧-orderTheoreticJoinSemilattice
d_'8743''45'orderTheoreticJoinSemilattice_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
d_'8743''45'orderTheoreticJoinSemilattice_182 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticJoinSemilattice_182 v2
du_'8743''45'orderTheoreticJoinSemilattice_182 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
du_'8743''45'orderTheoreticJoinSemilattice_182 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Bundles.C_constructor_96
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8729'__28 (coe v0))
      (coe du_'8743''45'isOrderTheoreticJoinSemilattice_178 (coe v0))
