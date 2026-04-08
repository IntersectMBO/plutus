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

module MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Base
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._._⊓_
d__'8851'__100 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8851'__100 ~v0 v1 ~v2 = du__'8851'__100 v1
du__'8851'__100 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8851'__100 v0
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
      (coe v0)
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.IsDistributiveLattice
d_IsDistributiveLattice_126 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.IsLattice
d_IsLattice_132 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.IsDistributiveLattice.isLattice
d_isLattice_354 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_isLattice_354 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158 (coe v0)
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.IsDistributiveLattice.∧-distrib-∨
d_'8743''45'distrib'45''8744'_378 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_378 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3162
      (coe v0)
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.IsDistributiveLattice.∨-distrib-∧
d_'8744''45'distrib'45''8743'_396 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_396 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3160
      (coe v0)
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.IsLattice.absorptive
d_absorptive_438 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_438 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3106 (coe v0)
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.IsLattice.isEquivalence
d_isEquivalence_440 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_440 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
      (coe v0)
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.IsLattice.∧-assoc
d_'8743''45'assoc_454 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_454 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
      (coe v0)
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.IsLattice.∧-comm
d_'8743''45'comm_456 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_456 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
      (coe v0)
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.IsLattice.∧-cong
d_'8743''45'cong_458 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_458 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
      (coe v0)
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.IsLattice.∨-assoc
d_'8744''45'assoc_466 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_466 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
      (coe v0)
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.IsLattice.∨-comm
d_'8744''45'comm_468 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_468 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
      (coe v0)
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.IsLattice.∨-cong
d_'8744''45'cong_470 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_470 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
      (coe v0)
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.⊓-isSemilattice
d_'8851''45'isSemilattice_798 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_'8851''45'isSemilattice_798 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'isSemilattice_798 v3 v4
du_'8851''45'isSemilattice_798 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_'8851''45'isSemilattice_798 v0 v1
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_616
      (coe v0) (coe v1)
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.⊓-semilattice
d_'8851''45'semilattice_800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_800 ~v0 ~v1 ~v2 v3 v4 ~v5
  = du_'8851''45'semilattice_800 v3 v4
du_'8851''45'semilattice_800 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
du_'8851''45'semilattice_800 v0 v1
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_618
      (coe v0) (coe v1)
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.⊓-isSemilattice
d_'8851''45'isSemilattice_804 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_'8851''45'isSemilattice_804 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'isSemilattice_804 v3 v5
du_'8851''45'isSemilattice_804 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_'8851''45'isSemilattice_804 v0 v1
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_616
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp._.⊓-semilattice
d_'8851''45'semilattice_806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_806 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_'8851''45'semilattice_806 v3 v5
du_'8851''45'semilattice_806 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
du_'8851''45'semilattice_806 v0 v1
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_618
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
         (coe v0))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
         (coe v1))
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.⊔-⊓-isLattice
d_'8852''45''8851''45'isLattice_808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_'8852''45''8851''45'isLattice_808 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8852''45''8851''45'isLattice_808 v3 v4 v5
du_'8852''45''8851''45'isLattice_808 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
du_'8852''45''8851''45'isLattice_808 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_constructor_3140
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
               (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2972
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_3060
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_3046
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2972
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_3060
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_3046
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'absorptive_3338
         (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.⊓-⊔-isLattice
d_'8851''45''8852''45'isLattice_810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_'8851''45''8852''45'isLattice_810 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8851''45''8852''45'isLattice_810 v3 v4 v5
du_'8851''45''8852''45'isLattice_810 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
du_'8851''45''8852''45'isLattice_810 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_constructor_3140
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
               (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2972
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_3060
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_3046
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2972
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_3060
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_3046
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
            (coe v0))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_186
            (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'absorptive_3340
         (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.⊓-⊔-isDistributiveLattice
d_'8851''45''8852''45'isDistributiveLattice_812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
d_'8851''45''8852''45'isDistributiveLattice_812 ~v0 ~v1 ~v2 v3 v4
                                                v5
  = du_'8851''45''8852''45'isDistributiveLattice_812 v3 v4 v5
du_'8851''45''8852''45'isDistributiveLattice_812 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
du_'8851''45''8852''45'isDistributiveLattice_812 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_constructor_3212
      (coe
         du_'8851''45''8852''45'isLattice_810 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45'distrib'45''8852'_3260
         (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45'distrib'45''8851'_3292
         (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.⊔-⊓-isDistributiveLattice
d_'8852''45''8851''45'isDistributiveLattice_814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
d_'8852''45''8851''45'isDistributiveLattice_814 ~v0 ~v1 ~v2 v3 v4
                                                v5
  = du_'8852''45''8851''45'isDistributiveLattice_814 v3 v4 v5
du_'8852''45''8851''45'isDistributiveLattice_814 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
du_'8852''45''8851''45'isDistributiveLattice_814 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_constructor_3212
      (coe
         du_'8852''45''8851''45'isLattice_808 (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45'distrib'45''8851'_3292
         (coe v0) (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45'distrib'45''8852'_3260
         (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.⊔-⊓-lattice
d_'8852''45''8851''45'lattice_816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512
d_'8852''45''8851''45'lattice_816 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8852''45''8851''45'lattice_816 v3 v4 v5
du_'8852''45''8851''45'lattice_816 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512
du_'8852''45''8851''45'lattice_816 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_constructor_592
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154
         (coe v2))
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
         (coe v1))
      (coe
         du_'8852''45''8851''45'isLattice_808 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.⊓-⊔-lattice
d_'8851''45''8852''45'lattice_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512
d_'8851''45''8852''45'lattice_818 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8851''45''8852''45'lattice_818 v3 v4 v5
du_'8851''45''8852''45'lattice_818 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512
du_'8851''45''8852''45'lattice_818 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_constructor_592
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
         (coe v1))
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154
         (coe v2))
      (coe
         du_'8851''45''8852''45'isLattice_810 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.⊔-⊓-distributiveLattice
d_'8852''45''8851''45'distributiveLattice_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_598
d_'8852''45''8851''45'distributiveLattice_820 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8852''45''8851''45'distributiveLattice_820 v3 v4 v5
du_'8852''45''8851''45'distributiveLattice_820 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_598
du_'8852''45''8851''45'distributiveLattice_820 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_constructor_692
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154
         (coe v2))
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
         (coe v1))
      (coe
         du_'8852''45''8851''45'isDistributiveLattice_814 (coe v0) (coe v1)
         (coe v2))
-- Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.⊓-⊔-distributiveLattice
d_'8851''45''8852''45'distributiveLattice_822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_598
d_'8851''45''8852''45'distributiveLattice_822 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8851''45''8852''45'distributiveLattice_822 v3 v4 v5
du_'8851''45''8852''45'distributiveLattice_822 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_138 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_598
du_'8851''45''8852''45'distributiveLattice_822 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_constructor_692
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
         (coe v1))
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8852'__154
         (coe v2))
      (coe
         du_'8851''45''8852''45'isDistributiveLattice_812 (coe v0) (coe v1)
         (coe v2))
