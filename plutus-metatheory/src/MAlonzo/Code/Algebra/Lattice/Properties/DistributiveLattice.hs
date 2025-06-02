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

module MAlonzo.Code.Algebra.Lattice.Properties.DistributiveLattice where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Lattice.Bundles qualified
import MAlonzo.Code.Algebra.Lattice.Properties.Lattice qualified
import MAlonzo.Code.Algebra.Lattice.Properties.Semilattice qualified
import MAlonzo.Code.Algebra.Lattice.Structures qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Lattice.Bundles qualified
import MAlonzo.Code.Relation.Binary.Lattice.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Lattice.Properties.DistributiveLattice._.IsDistributiveLattice
d_IsDistributiveLattice_230 a0 a1 a2 a3 a4 = ()
-- Algebra.Lattice.Properties.DistributiveLattice._.IsDistributiveLattice.isLattice
d_isLattice_454 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
d_isLattice_454 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v0)
-- Algebra.Lattice.Properties.DistributiveLattice._.IsDistributiveLattice.∧-distrib-∨
d_'8743''45'distrib'45''8744'_478 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_478 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3052
      (coe v0)
-- Algebra.Lattice.Properties.DistributiveLattice._.IsDistributiveLattice.∨-distrib-∧
d_'8744''45'distrib'45''8743'_496 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_496 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3050
      (coe v0)
-- Algebra.Lattice.Properties.DistributiveLattice._.poset
d_poset_686 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_686 ~v0 ~v1 v2 = du_poset_686 v2
du_poset_686 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_686 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_poset_162
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_3194
            (coe v1)))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-idem
d_'8743''45'idem_688 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny
d_'8743''45'idem_688 ~v0 ~v1 v2 = du_'8743''45'idem_688 v2
du_'8743''45'idem_688 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny
du_'8743''45'idem_688 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'idem_3182
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-isBand
d_'8743''45'isBand_690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8743''45'isBand_690 ~v0 ~v1 v2 = du_'8743''45'isBand_690 v2
du_'8743''45'isBand_690 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_'8743''45'isBand_690 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isBand_3190
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-isMagma
d_'8743''45'isMagma_692 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8743''45'isMagma_692 ~v0 ~v1 v2 = du_'8743''45'isMagma_692 v2
du_'8743''45'isMagma_692 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'8743''45'isMagma_692 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isMagma_3186
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-isOrderTheoreticJoinSemilattice
d_'8743''45'isOrderTheoreticJoinSemilattice_694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_'8743''45'isOrderTheoreticJoinSemilattice_694 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticJoinSemilattice_694 v2
du_'8743''45'isOrderTheoreticJoinSemilattice_694 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_'8743''45'isOrderTheoreticJoinSemilattice_694 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_3194
            (coe v1)))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-isOrderTheoreticMeetSemilattice
d_'8743''45'isOrderTheoreticMeetSemilattice_696 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
d_'8743''45'isOrderTheoreticMeetSemilattice_696 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticMeetSemilattice_696 v2
du_'8743''45'isOrderTheoreticMeetSemilattice_696 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
du_'8743''45'isOrderTheoreticMeetSemilattice_696 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticMeetSemilattice_176
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_3194
            (coe v1)))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-isSemigroup
d_'8743''45'isSemigroup_698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8743''45'isSemigroup_698 ~v0 ~v1 v2
  = du_'8743''45'isSemigroup_698 v2
du_'8743''45'isSemigroup_698 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'8743''45'isSemigroup_698 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isSemigroup_3188
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-isSemilattice
d_'8743''45'isSemilattice_700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_'8743''45'isSemilattice_700 ~v0 ~v1 v2
  = du_'8743''45'isSemilattice_700 v2
du_'8743''45'isSemilattice_700 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
du_'8743''45'isSemilattice_700 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'isSemilattice_3192
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-orderTheoreticJoinSemilattice
d_'8743''45'orderTheoreticJoinSemilattice_702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
d_'8743''45'orderTheoreticJoinSemilattice_702 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticJoinSemilattice_702 v2
du_'8743''45'orderTheoreticJoinSemilattice_702 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
du_'8743''45'orderTheoreticJoinSemilattice_702 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticJoinSemilattice_182
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_3194
            (coe v1)))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-orderTheoreticMeetSemilattice
d_'8743''45'orderTheoreticMeetSemilattice_704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_200
d_'8743''45'orderTheoreticMeetSemilattice_704 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticMeetSemilattice_704 v2
du_'8743''45'orderTheoreticMeetSemilattice_704 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_200
du_'8743''45'orderTheoreticMeetSemilattice_704 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticMeetSemilattice_180
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_3194
            (coe v1)))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-semilattice
d_'8743''45'semilattice_706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8743''45'semilattice_706 ~v0 ~v1 v2
  = du_'8743''45'semilattice_706 v2
du_'8743''45'semilattice_706 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
du_'8743''45'semilattice_706 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45'semilattice_3194
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-∨-isLattice
d_'8743''45''8744''45'isLattice_708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
d_'8743''45''8744''45'isLattice_708 ~v0 ~v1 v2
  = du_'8743''45''8744''45'isLattice_708 v2
du_'8743''45''8744''45'isLattice_708 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
du_'8743''45''8744''45'isLattice_708 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45''8744''45'isLattice_3230
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-∨-lattice
d_'8743''45''8744''45'lattice_710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
d_'8743''45''8744''45'lattice_710 ~v0 ~v1 v2
  = du_'8743''45''8744''45'lattice_710 v2
du_'8743''45''8744''45'lattice_710 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
du_'8743''45''8744''45'lattice_710 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45''8744''45'lattice_3232
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∨-idem
d_'8744''45'idem_712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny
d_'8744''45'idem_712 ~v0 ~v1 v2 = du_'8744''45'idem_712 v2
du_'8744''45'idem_712 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny
du_'8744''45'idem_712 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'idem_3206
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∨-isBand
d_'8744''45'isBand_714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8744''45'isBand_714 ~v0 ~v1 v2 = du_'8744''45'isBand_714 v2
du_'8744''45'isBand_714 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_'8744''45'isBand_714 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isBand_3214
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∨-isMagma
d_'8744''45'isMagma_716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8744''45'isMagma_716 ~v0 ~v1 v2 = du_'8744''45'isMagma_716 v2
du_'8744''45'isMagma_716 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'8744''45'isMagma_716 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isMagma_3210
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-isOrderTheoreticJoinSemilattice
d_'8743''45'isOrderTheoreticJoinSemilattice_718 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_'8743''45'isOrderTheoreticJoinSemilattice_718 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticJoinSemilattice_718 v2
du_'8743''45'isOrderTheoreticJoinSemilattice_718 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_'8743''45'isOrderTheoreticJoinSemilattice_718 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_3218
            (coe v1)))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-isOrderTheoreticMeetSemilattice
d_'8743''45'isOrderTheoreticMeetSemilattice_720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
d_'8743''45'isOrderTheoreticMeetSemilattice_720 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticMeetSemilattice_720 v2
du_'8743''45'isOrderTheoreticMeetSemilattice_720 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
du_'8743''45'isOrderTheoreticMeetSemilattice_720 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticMeetSemilattice_176
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_3218
            (coe v1)))
-- Algebra.Lattice.Properties.DistributiveLattice._.∨-isSemigroup
d_'8744''45'isSemigroup_722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8744''45'isSemigroup_722 ~v0 ~v1 v2
  = du_'8744''45'isSemigroup_722 v2
du_'8744''45'isSemigroup_722 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'8744''45'isSemigroup_722 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isSemigroup_3212
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∨-isSemilattice
d_'8744''45'isSemilattice_724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_'8744''45'isSemilattice_724 ~v0 ~v1 v2
  = du_'8744''45'isSemilattice_724 v2
du_'8744''45'isSemilattice_724 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
du_'8744''45'isSemilattice_724 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'isSemilattice_3216
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-orderTheoreticJoinSemilattice
d_'8743''45'orderTheoreticJoinSemilattice_726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
d_'8743''45'orderTheoreticJoinSemilattice_726 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticJoinSemilattice_726 v2
du_'8743''45'orderTheoreticJoinSemilattice_726 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
du_'8743''45'orderTheoreticJoinSemilattice_726 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticJoinSemilattice_182
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_3218
            (coe v1)))
-- Algebra.Lattice.Properties.DistributiveLattice._.∧-orderTheoreticMeetSemilattice
d_'8743''45'orderTheoreticMeetSemilattice_728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_200
d_'8743''45'orderTheoreticMeetSemilattice_728 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticMeetSemilattice_728 v2
du_'8743''45'orderTheoreticMeetSemilattice_728 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_200
du_'8743''45'orderTheoreticMeetSemilattice_728 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticMeetSemilattice_180
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_3218
            (coe v1)))
-- Algebra.Lattice.Properties.DistributiveLattice._.∨-semilattice
d_'8744''45'semilattice_730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8744''45'semilattice_730 ~v0 ~v1 v2
  = du_'8744''45'semilattice_730 v2
du_'8744''45'semilattice_730 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
du_'8744''45'semilattice_730 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45'semilattice_3218
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∨-∧-isOrderTheoreticLattice
d_'8744''45''8743''45'isOrderTheoreticLattice_732 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
d_'8744''45''8743''45'isOrderTheoreticLattice_732 ~v0 ~v1 v2
  = du_'8744''45''8743''45'isOrderTheoreticLattice_732 v2
du_'8744''45''8743''45'isOrderTheoreticLattice_732 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
du_'8744''45''8743''45'isOrderTheoreticLattice_732 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45''8743''45'isOrderTheoreticLattice_3244
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice._.∨-∧-orderTheoreticLattice
d_'8744''45''8743''45'orderTheoreticLattice_734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_Lattice_386
d_'8744''45''8743''45'orderTheoreticLattice_734 ~v0 ~v1 v2
  = du_'8744''45''8743''45'orderTheoreticLattice_734 v2
du_'8744''45''8743''45'orderTheoreticLattice_734 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_Lattice_386
du_'8744''45''8743''45'orderTheoreticLattice_734 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8744''45''8743''45'orderTheoreticLattice_3300
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0))
-- Algebra.Lattice.Properties.DistributiveLattice.∧-∨-isDistributiveLattice
d_'8743''45''8744''45'isDistributiveLattice_736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036
d_'8743''45''8744''45'isDistributiveLattice_736 ~v0 ~v1 v2
  = du_'8743''45''8744''45'isDistributiveLattice_736 v2
du_'8743''45''8744''45'isDistributiveLattice_736 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036
du_'8743''45''8744''45'isDistributiveLattice_736 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_IsDistributiveLattice'46'constructor_40943
      (coe
         MAlonzo.Code.Algebra.Lattice.Properties.Lattice.du_'8743''45''8744''45'isLattice_3230
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3052
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isDistributiveLattice_608
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3050
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isDistributiveLattice_608
            (coe v0)))
-- Algebra.Lattice.Properties.DistributiveLattice.∧-∨-distributiveLattice
d_'8743''45''8744''45'distributiveLattice_738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
d_'8743''45''8744''45'distributiveLattice_738 ~v0 ~v1 v2
  = du_'8743''45''8744''45'distributiveLattice_738 v2
du_'8743''45''8744''45'distributiveLattice_738 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
du_'8743''45''8744''45'distributiveLattice_738 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_DistributiveLattice'46'constructor_9515
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__606 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__604 (coe v0))
      (coe du_'8743''45''8744''45'isDistributiveLattice_736 (coe v0))
