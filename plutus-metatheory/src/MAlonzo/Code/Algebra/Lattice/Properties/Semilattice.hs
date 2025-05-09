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

module MAlonzo.Code.Algebra.Lattice.Properties.Semilattice where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Lattice.Bundles qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Construct.NaturalOrder.Left qualified
import MAlonzo.Code.Relation.Binary.Lattice.Bundles qualified
import MAlonzo.Code.Relation.Binary.Lattice.Structures qualified
import MAlonzo.Code.Relation.Binary.Properties.Poset qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Lattice.Properties.Semilattice.poset
d_poset_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_162 ~v0 ~v1 v2 = du_poset_162 v2
du_poset_162 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_162 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.NaturalOrder.Left.du_poset_3784
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
-- Algebra.Lattice.Properties.Semilattice._._≳_
d__'8819'__168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  AgdaAny -> AgdaAny -> ()
d__'8819'__168 = erased
-- Algebra.Lattice.Properties.Semilattice.∧-isOrderTheoreticMeetSemilattice
d_'8743''45'isOrderTheoreticMeetSemilattice_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
d_'8743''45'isOrderTheoreticMeetSemilattice_176 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticMeetSemilattice_176 v2
du_'8743''45'isOrderTheoreticMeetSemilattice_176 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
du_'8743''45'isOrderTheoreticMeetSemilattice_176 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.C_IsMeetSemilattice'46'constructor_7577
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
         (coe du_poset_162 (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.NaturalOrder.Left.du_infimum_3640
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
      MAlonzo.Code.Relation.Binary.Lattice.Structures.C_IsJoinSemilattice'46'constructor_527
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Poset.du_'8805''45'isPartialOrder_142
         (coe du_poset_162 (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.NaturalOrder.Left.du_infimum_3640
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8729'__28 (coe v0))
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isSemilattice_30 (coe v0)))
-- Algebra.Lattice.Properties.Semilattice.∧-orderTheoreticMeetSemilattice
d_'8743''45'orderTheoreticMeetSemilattice_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_200
d_'8743''45'orderTheoreticMeetSemilattice_180 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticMeetSemilattice_180 v2
du_'8743''45'orderTheoreticMeetSemilattice_180 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_200
du_'8743''45'orderTheoreticMeetSemilattice_180 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Bundles.C_MeetSemilattice'46'constructor_4629
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
      MAlonzo.Code.Relation.Binary.Lattice.Bundles.C_JoinSemilattice'46'constructor_371
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8729'__28 (coe v0))
      (coe du_'8743''45'isOrderTheoreticJoinSemilattice_178 (coe v0))
