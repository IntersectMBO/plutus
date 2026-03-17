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

module MAlonzo.Code.Algebra.Lattice.Structures.Biased where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Consequences.Base
import qualified MAlonzo.Code.Algebra.Consequences.Setoid
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Lattice.Structures.Biased._._DistributesOverʳ_
d__DistributesOver'691'__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'691'__18 = erased
-- Algebra.Lattice.Structures.Biased._.Absorptive
d_Absorptive_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Absorptive_20 = erased
-- Algebra.Lattice.Structures.Biased._.Congruent₁
d_Congruent'8321'_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> ()
d_Congruent'8321'_26 = erased
-- Algebra.Lattice.Structures.Biased._.RightInverse
d_RightInverse_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightInverse_28 = erased
-- Algebra.Lattice.Structures.Biased._.IsBooleanAlgebra
d_IsBooleanAlgebra_32 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice
d_IsDistributiveLattice_34 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice
d_IsJoinSemilattice_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_IsJoinSemilattice_36 = erased
-- Algebra.Lattice.Structures.Biased._.IsLattice
d_IsLattice_38 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice
d_IsMeetSemilattice_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_IsMeetSemilattice_40 = erased
-- Algebra.Lattice.Structures.Biased._.IsBooleanAlgebra.isDistributiveLattice
d_isDistributiveLattice_46 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3134 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
d_isDistributiveLattice_46 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
      (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsBooleanAlgebra.¬-cong
d_'172''45'cong_62 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3134 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'cong_62 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3160
      (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsBooleanAlgebra.∧-complement
d_'8743''45'complement_70 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3134 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'complement_70 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'complement_3158
      (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsBooleanAlgebra.∨-complement
d_'8744''45'complement_94 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3134 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'complement_94 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'complement_3156
      (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.isLattice
d_isLattice_118 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
d_isLattice_118 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.isPartialEquivalence
d_isPartialEquivalence_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_120 v6
du_isPartialEquivalence_120 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_120 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
            (coe v1)))
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.reflexive
d_reflexive_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_124 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_124 v6
du_reflexive_124 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_124 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
              (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe
              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
              (coe v1))
           v2)
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8743''45'absorbs'45''8744'_130 v6
du_'8743''45'absorbs'45''8744'_130 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_130 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3036
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v0))
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.∧-congʳ
d_'8743''45'cong'691'_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'691'_138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8743''45'cong'691'_138 v6
du_'8743''45'cong'691'_138 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'691'_138 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3042
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v0))
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.∧-congˡ
d_'8743''45'cong'737'_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'737'_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8743''45'cong'737'_140 v6
du_'8743''45'cong'737'_140 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'737'_140 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3038
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v0))
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.∧-distrib-∨
d_'8743''45'distrib'45''8744'_142 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_142 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3074
      (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.∧-distribʳ-∨
d_'8743''45'distrib'691''45''8744'_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'691''45''8744'_144 ~v0 ~v1 ~v2 ~v3
  = du_'8743''45'distrib'691''45''8744'_144
du_'8743''45'distrib'691''45''8744'_144 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'691''45''8744'_144 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'691''45''8744'_3122
      v2
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8744'_146 ~v0 ~v1 ~v2 ~v3
  = du_'8743''45'distrib'737''45''8744'_146
du_'8743''45'distrib'737''45''8744'_146 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'737''45''8744'_146 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3120
      v2
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8744''45'absorbs'45''8743'_148 v6
du_'8744''45'absorbs'45''8743'_148 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_148 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3034
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v0))
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.∨-congʳ
d_'8744''45'cong'691'_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'691'_156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8744''45'cong'691'_156 v6
du_'8744''45'cong'691'_156 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'691'_156 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3050
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v0))
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.∨-congˡ
d_'8744''45'cong'737'_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'737'_158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8744''45'cong'737'_158 v6
du_'8744''45'cong'737'_158 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'737'_158 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3046
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v0))
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.∨-distrib-∧
d_'8744''45'distrib'45''8743'_160 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_160 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3072
      (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'691''45''8743'_162 ~v0 ~v1 ~v2 ~v3
  = du_'8744''45'distrib'691''45''8743'_162
du_'8744''45'distrib'691''45''8743'_162 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'691''45''8743'_162 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3118
      v2
-- Algebra.Lattice.Structures.Biased._.IsDistributiveLattice.∨-distribˡ-∧
d_'8744''45'distrib'737''45''8743'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'737''45''8743'_164 ~v0 ~v1 ~v2 ~v3
  = du_'8744''45'distrib'737''45''8743'_164
du_'8744''45'distrib'737''45''8743'_164 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'737''45''8743'_164 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'737''45''8743'_3116
      v2
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice.assoc
d_assoc_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_168 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_assoc_168 v5
du_assoc_168 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_168 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0)))
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice.idem
d_idem_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny
d_idem_172 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_idem_172 v5
du_idem_172 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny
du_idem_172 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_idem_516
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0))
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice.isEquivalence
d_isEquivalence_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_176 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_176 v5
du_isEquivalence_176 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_176 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0))))
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice.isMagma
d_isMagma_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_178 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_178 v5
du_isMagma_178 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_178 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_478
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0)))
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice.isPartialEquivalence
d_isPartialEquivalence_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_180 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_180 v5
du_isPartialEquivalence_180 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_180 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v3)))))
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice.isSemigroup
d_isSemigroup_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_182 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_182 v5
du_isSemigroup_182 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_182 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0))
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice.refl
d_refl_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny
d_refl_184 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_184 v5
du_refl_184 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny
du_refl_184 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0)))))
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice.reflexive
d_reflexive_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_186 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_186 v5
du_reflexive_186 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_186 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v3))
                 v4)))
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice.setoid
d_setoid_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_188 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_188 v5
du_setoid_188 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_188 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_200
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v2))))
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice.sym
d_sym_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_190 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_sym_190 v5
du_sym_190 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_190 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0)))))
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice.trans
d_trans_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_192 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_trans_192 v5
du_trans_192 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_192 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0)))))
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice.∙-cong
d_'8729''45'cong_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_194 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong_194 v5
du_'8729''45'cong_194 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_194 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0))))
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice.∙-congʳ
d_'8729''45'cong'691'_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_196 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_196 v5
du_'8729''45'cong'691'_196 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_196 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v2) in
          coe
            (let v4
                   = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (coe v4))))))))
-- Algebra.Lattice.Structures.Biased._.IsJoinSemilattice.∙-congˡ
d_'8729''45'cong'737'_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_198 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_198 v5
du_'8729''45'cong'737'_198 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_198 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v2) in
          coe
            (let v4
                   = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (coe v4))))))))
-- Algebra.Lattice.Structures.Biased._.IsLattice.absorptive
d_absorptive_202 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_202 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3020 (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsLattice.isEquivalence
d_isEquivalence_204 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_204 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
      (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsLattice.isPartialEquivalence
d_isPartialEquivalence_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_206 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_206 v6
du_isPartialEquivalence_206 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_206 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
         (coe v0))
-- Algebra.Lattice.Structures.Biased._.IsLattice.reflexive
d_reflexive_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_210 v6
du_reflexive_210 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_210 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
         (coe v0))
      v1
-- Algebra.Lattice.Structures.Biased._.IsLattice.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_216 ~v0 ~v1 ~v2 ~v3
  = du_'8743''45'absorbs'45''8744'_216
du_'8743''45'absorbs'45''8744'_216 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_216 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3036
      v2
-- Algebra.Lattice.Structures.Biased._.IsLattice.∧-assoc
d_'8743''45'assoc_218 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_218 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3016
      (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsLattice.∧-comm
d_'8743''45'comm_220 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_220 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3014
      (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsLattice.∧-cong
d_'8743''45'cong_222 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_222 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3018
      (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsLattice.∧-congʳ
d_'8743''45'cong'691'_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'691'_224 ~v0 ~v1 ~v2 ~v3
  = du_'8743''45'cong'691'_224
du_'8743''45'cong'691'_224 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'691'_224 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3042
      v2 v3 v4 v5 v6
-- Algebra.Lattice.Structures.Biased._.IsLattice.∧-congˡ
d_'8743''45'cong'737'_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'737'_226 ~v0 ~v1 ~v2 ~v3
  = du_'8743''45'cong'737'_226
du_'8743''45'cong'737'_226 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'737'_226 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3038
      v2 v3 v4 v5 v6
-- Algebra.Lattice.Structures.Biased._.IsLattice.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_228 ~v0 ~v1 ~v2 ~v3
  = du_'8744''45'absorbs'45''8743'_228
du_'8744''45'absorbs'45''8743'_228 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_228 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3034
      v2
-- Algebra.Lattice.Structures.Biased._.IsLattice.∨-assoc
d_'8744''45'assoc_230 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_230 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3010
      (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsLattice.∨-comm
d_'8744''45'comm_232 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_232 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3008
      (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsLattice.∨-cong
d_'8744''45'cong_234 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_234 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3012
      (coe v0)
-- Algebra.Lattice.Structures.Biased._.IsLattice.∨-congʳ
d_'8744''45'cong'691'_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'691'_236 ~v0 ~v1 ~v2 ~v3
  = du_'8744''45'cong'691'_236
du_'8744''45'cong'691'_236 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'691'_236 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3050
      v2 v3 v4 v5 v6
-- Algebra.Lattice.Structures.Biased._.IsLattice.∨-congˡ
d_'8744''45'cong'737'_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'737'_238 ~v0 ~v1 ~v2 ~v3
  = du_'8744''45'cong'737'_238
du_'8744''45'cong'737'_238 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'737'_238 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3046
      v2 v3 v4 v5 v6
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice.assoc
d_assoc_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_242 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_assoc_242 v5
du_assoc_242 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_242 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0)))
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice.idem
d_idem_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny
d_idem_246 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_idem_246 v5
du_idem_246 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny
du_idem_246 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_idem_516
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0))
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice.isEquivalence
d_isEquivalence_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_250 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isEquivalence_250 v5
du_isEquivalence_250 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_250 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0))))
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice.isMagma
d_isMagma_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_252 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isMagma_252 v5
du_isMagma_252 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_252 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_478
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0)))
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice.isPartialEquivalence
d_isPartialEquivalence_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_254 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_isPartialEquivalence_254 v5
du_isPartialEquivalence_254 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_254 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v3)))))
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice.isSemigroup
d_isSemigroup_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_256 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isSemigroup_256 v5
du_isSemigroup_256 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_256 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
      (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0))
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice.refl
d_refl_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny
d_refl_258 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_refl_258 v5
du_refl_258 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny
du_refl_258 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0)))))
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice.reflexive
d_reflexive_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_260 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_reflexive_260 v5
du_reflexive_260 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_260 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v3))
                 v4)))
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice.setoid
d_setoid_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_262 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_setoid_262 v5
du_setoid_262 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_262 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_setoid_200
            (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v2))))
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice.sym
d_sym_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_264 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_sym_264 v5
du_sym_264 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_264 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0)))))
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice.trans
d_trans_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_266 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_trans_266 v5
du_trans_266 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_266 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0)))))
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice.∙-cong
d_'8729''45'cong_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_268 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong_268 v5
du_'8729''45'cong_268 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_268 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0))))
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice.∙-congʳ
d_'8729''45'cong'691'_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_270 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'691'_270 v5
du_'8729''45'cong'691'_270 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_270 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v2) in
          coe
            (let v4
                   = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (coe v4))))))))
-- Algebra.Lattice.Structures.Biased._.IsMeetSemilattice.∙-congˡ
d_'8729''45'cong'737'_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_272 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8729''45'cong'737'_272 v5
du_'8729''45'cong'737'_272 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_272 v0
  = let v1 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v2) in
          coe
            (let v4
                   = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                     (coe v5)
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (coe v4))))))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂
d_IsLattice'8322'_288 a0 a1 a2 a3 a4 a5 = ()
data T_IsLattice'8322'_288
  = C_IsLattice'8322''46'constructor_2829 MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588
                                          MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588
                                          MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
-- Algebra.Lattice.Structures.Biased.IsLattice₂.isJoinSemilattice
d_isJoinSemilattice_300 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588
d_isJoinSemilattice_300 v0
  = case coe v0 of
      C_IsLattice'8322''46'constructor_2829 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.Biased.IsLattice₂.isMeetSemilattice
d_isMeetSemilattice_302 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588
d_isMeetSemilattice_302 v0
  = case coe v0 of
      C_IsLattice'8322''46'constructor_2829 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.Biased.IsLattice₂.absorptive
d_absorptive_304 ::
  T_IsLattice'8322'_288 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_304 v0
  = case coe v0 of
      C_IsLattice'8322''46'constructor_2829 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.assoc
d_assoc_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_assoc_308 v6
du_assoc_308 ::
  T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_308 v0
  = let v1 = d_isMeetSemilattice_302 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.comm
d_comm_310 ::
  T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_310 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_598
      (coe d_isMeetSemilattice_302 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.idem
d_idem_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny
d_idem_312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_idem_312 v6
du_idem_312 :: T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny
du_idem_312 v0
  = let v1 = d_isMeetSemilattice_302 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_idem_516
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1)))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.isBand
d_isBand_314 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506
d_isBand_314 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isBand_596
      (coe d_isMeetSemilattice_302 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.isEquivalence
d_isEquivalence_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_316 v6
du_isEquivalence_316 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_316 v0
  = let v1 = d_isMeetSemilattice_302 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1)))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.isMagma
d_isMagma_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_318 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isMagma_318 v6
du_isMagma_318 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_318 v0
  = let v1 = d_isMeetSemilattice_302 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.isPartialEquivalence
d_isPartialEquivalence_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_320 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_320 v6
du_isPartialEquivalence_320 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_320 v0
  = let v1 = d_isMeetSemilattice_302 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.isSemigroup
d_isSemigroup_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isSemigroup_322 v6
du_isSemigroup_322 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_322 v0
  = let v1 = d_isMeetSemilattice_302 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1)))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.refl
d_refl_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny
d_refl_324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_324 v6
du_refl_324 :: T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny
du_refl_324 v0
  = let v1 = d_isMeetSemilattice_302 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1))))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.reflexive
d_reflexive_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_326 v6
du_reflexive_326 ::
  T_IsLattice'8322'_288 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_326 v0
  = let v1 = d_isMeetSemilattice_302 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))
                    v5))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.setoid
d_setoid_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_328 v6
du_setoid_328 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_328 v0
  = let v1 = d_isMeetSemilattice_302 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_200
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v3)))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.sym
d_sym_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_330 v6
du_sym_330 ::
  T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_330 v0
  = let v1 = d_isMeetSemilattice_302 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1))))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.trans
d_trans_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_332 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_332 v6
du_trans_332 ::
  T_IsLattice'8322'_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_332 v0
  = let v1 = d_isMeetSemilattice_302 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1))))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.∙-cong
d_'8729''45'cong_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong_334 v6
du_'8729''45'cong_334 ::
  T_IsLattice'8322'_288 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_334 v0
  = let v1 = d_isMeetSemilattice_302 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1)))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.∙-congʳ
d_'8729''45'cong'691'_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_336 v6
du_'8729''45'cong'691'_336 ::
  T_IsLattice'8322'_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_336 v0
  = let v1 = d_isMeetSemilattice_302 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (coe v5)))))))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.ML.∙-congˡ
d_'8729''45'cong'737'_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_338 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_338 v6
du_'8729''45'cong'737'_338 ::
  T_IsLattice'8322'_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_338 v0
  = let v1 = d_isMeetSemilattice_302 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (coe v5)))))))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.assoc
d_assoc_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_342 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_assoc_342 v6
du_assoc_342 ::
  T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_342 v0
  = let v1 = d_isJoinSemilattice_300 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.comm
d_comm_344 ::
  T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_344 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_598
      (coe d_isJoinSemilattice_300 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.idem
d_idem_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny
d_idem_346 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_idem_346 v6
du_idem_346 :: T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny
du_idem_346 v0
  = let v1 = d_isJoinSemilattice_300 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_idem_516
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1)))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.isBand
d_isBand_348 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_506
d_isBand_348 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isBand_596
      (coe d_isJoinSemilattice_300 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.isEquivalence
d_isEquivalence_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isEquivalence_350 v6
du_isEquivalence_350 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_350 v0
  = let v1 = d_isJoinSemilattice_300 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1)))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.isMagma
d_isMagma_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isMagma_352 v6
du_isMagma_352 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_352 v0
  = let v1 = d_isJoinSemilattice_300 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.isPartialEquivalence
d_isPartialEquivalence_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_354 v6
du_isPartialEquivalence_354 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_354 v0
  = let v1 = d_isJoinSemilattice_300 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.isSemigroup
d_isSemigroup_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isSemigroup_356 v6
du_isSemigroup_356 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_356 v0
  = let v1 = d_isJoinSemilattice_300 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1)))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.refl
d_refl_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny
d_refl_358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_refl_358 v6
du_refl_358 :: T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny
du_refl_358 v0
  = let v1 = d_isJoinSemilattice_300 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1))))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.reflexive
d_reflexive_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_360 v6
du_reflexive_360 ::
  T_IsLattice'8322'_288 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_360 v0
  = let v1 = d_isJoinSemilattice_300 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))
                    v5))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.setoid
d_setoid_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_362 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_362 v6
du_setoid_362 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_362 v0
  = let v1 = d_isJoinSemilattice_300 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_200
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v3)))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.sym
d_sym_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_364 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sym_364 v6
du_sym_364 ::
  T_IsLattice'8322'_288 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_364 v0
  = let v1 = d_isJoinSemilattice_300 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1))))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.trans
d_trans_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_trans_366 v6
du_trans_366 ::
  T_IsLattice'8322'_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_366 v0
  = let v1 = d_isJoinSemilattice_300 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1))))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.∙-cong
d_'8729''45'cong_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_368 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong_368 v6
du_'8729''45'cong_368 ::
  T_IsLattice'8322'_288 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_368 v0
  = let v1 = d_isJoinSemilattice_300 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1)))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.∙-congʳ
d_'8729''45'cong'691'_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'691'_370 v6
du_'8729''45'cong'691'_370 ::
  T_IsLattice'8322'_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_370 v0
  = let v1 = d_isJoinSemilattice_300 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (coe v5)))))))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.JL.∙-congˡ
d_'8729''45'cong'737'_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_372 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8729''45'cong'737'_372 v6
du_'8729''45'cong'737'_372 ::
  T_IsLattice'8322'_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_372 v0
  = let v1 = d_isJoinSemilattice_300 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_514 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (coe v5)))))))))
-- Algebra.Lattice.Structures.Biased.IsLattice₂.isLattice₂
d_isLattice'8322'_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
d_isLattice'8322'_374 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isLattice'8322'_374 v6
du_isLattice'8322'_374 ::
  T_IsLattice'8322'_288 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
du_isLattice'8322'_374 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_IsLattice'46'constructor_36909
      (let v1 = d_isMeetSemilattice_302 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1))))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_comm_598
         (coe d_isJoinSemilattice_300 (coe v0)))
      (let v1 = d_isJoinSemilattice_300 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1)))))
      (let v1 = d_isJoinSemilattice_300 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1))))))
      (coe
         MAlonzo.Code.Algebra.Structures.d_comm_598
         (coe d_isMeetSemilattice_302 (coe v0)))
      (let v1 = d_isMeetSemilattice_302 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1)))))
      (let v1 = d_isMeetSemilattice_302 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_514
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_596 (coe v1))))))
      (coe d_absorptive_304 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ
d_IsDistributiveLattice'691''690''7504'_380 a0 a1 a2 a3 a4 a5 = ()
data T_IsDistributiveLattice'691''690''7504'_380
  = C_IsDistributiveLattice'691''690''7504''46'constructor_5653 MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
                                                                (AgdaAny ->
                                                                 AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ.isLattice
d_isLattice_390 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
d_isLattice_390 v0
  = case coe v0 of
      C_IsDistributiveLattice'691''690''7504''46'constructor_5653 v1 v2
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_392 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'691''45''8743'_392 v0
  = case coe v0 of
      C_IsDistributiveLattice'691''690''7504''46'constructor_5653 v1 v2
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.absorptive
d_absorptive_396 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_396 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3020
      (coe d_isLattice_390 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.isEquivalence
d_isEquivalence_398 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_398 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
      (coe d_isLattice_390 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.isPartialEquivalence
d_isPartialEquivalence_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_400 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialEquivalence_400 v6
du_isPartialEquivalence_400 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_400 v0
  = let v1 = d_isLattice_390 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
            (coe v1)))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.refl
d_refl_402 ::
  T_IsDistributiveLattice'691''690''7504'_380 -> AgdaAny -> AgdaAny
d_refl_402 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
         (coe d_isLattice_390 (coe v0)))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.reflexive
d_reflexive_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_404 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_reflexive_404 v6
du_reflexive_404 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_404 v0
  = let v1 = d_isLattice_390 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe
              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
              (coe v1))
           v2)
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.sym
d_sym_406 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_406 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
         (coe d_isLattice_390 (coe v0)))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.trans
d_trans_408 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_408 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
         (coe d_isLattice_390 (coe v0)))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_410 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8743''45'absorbs'45''8744'_410 v6
du_'8743''45'absorbs'45''8744'_410 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_410 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3036
      (coe d_isLattice_390 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.∧-assoc
d_'8743''45'assoc_412 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_412 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3016
      (coe d_isLattice_390 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.∧-comm
d_'8743''45'comm_414 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_414 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3014
      (coe d_isLattice_390 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.∧-cong
d_'8743''45'cong_416 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_416 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3018
      (coe d_isLattice_390 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.∧-congʳ
d_'8743''45'cong'691'_418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'691'_418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8743''45'cong'691'_418 v6
du_'8743''45'cong'691'_418 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'691'_418 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3042
      (coe d_isLattice_390 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.∧-congˡ
d_'8743''45'cong'737'_420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'737'_420 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8743''45'cong'737'_420 v6
du_'8743''45'cong'737'_420 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'737'_420 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3038
      (coe d_isLattice_390 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8744''45'absorbs'45''8743'_422 v6
du_'8744''45'absorbs'45''8743'_422 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_422 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3034
      (coe d_isLattice_390 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.∨-assoc
d_'8744''45'assoc_424 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_424 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3010
      (coe d_isLattice_390 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.∨-comm
d_'8744''45'comm_426 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_426 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3008
      (coe d_isLattice_390 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.∨-cong
d_'8744''45'cong_428 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_428 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3012
      (coe d_isLattice_390 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.∨-congʳ
d_'8744''45'cong'691'_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'691'_430 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8744''45'cong'691'_430 v6
du_'8744''45'cong'691'_430 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'691'_430 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3050
      (coe d_isLattice_390 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ._.∨-congˡ
d_'8744''45'cong'737'_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'737'_432 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8744''45'cong'737'_432 v6
du_'8744''45'cong'737'_432 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'737'_432 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3046
      (coe d_isLattice_390 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ.setoid
d_setoid_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_434 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_setoid_434 v6
du_setoid_434 ::
  T_IsDistributiveLattice'691''690''7504'_380 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_434 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_761
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
         (coe d_isLattice_390 (coe v0)))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ.∨-distrib-∧
d_'8744''45'distrib'45''8743'_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_436 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'8744''45'distrib'45''8743'_436 v4 v5 v6
du_'8744''45'distrib'45''8743'_436 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8744''45'distrib'45''8743'_436 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'distr'691''8658'distr_560
      (coe du_setoid_434 (coe v2)) (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3018
         (coe d_isLattice_390 (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3008
         (coe d_isLattice_390 (coe v2)))
      (coe d_'8744''45'distrib'691''45''8743'_392 (coe v2))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8744'_438 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'8743''45'distrib'737''45''8744'_438 v4 v5 v6
du_'8743''45'distrib'737''45''8744'_438 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'737''45''8744'_438 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_distrib'8743'absorbs'8658'distrib'737'_600
      (coe du_setoid_434 (coe v2)) (coe v1) (coe v0)
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3018
         (coe d_isLattice_390 (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3016
         (coe d_isLattice_390 (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3008
         (coe d_isLattice_390 (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3036
         (coe d_isLattice_390 (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3034
         (coe d_isLattice_390 (coe v2)))
      (coe du_'8744''45'distrib'45''8743'_436 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ.∧-distrib-∨
d_'8743''45'distrib'45''8744'_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_440 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'8743''45'distrib'45''8744'_440 v4 v5 v6
du_'8743''45'distrib'45''8744'_440 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8743''45'distrib'45''8744'_440 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'distr'737''8658'distr_556
      (coe du_setoid_434 (coe v2)) (coe v1) (coe v0)
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3012
         (coe d_isLattice_390 (coe v2)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3014
         (coe d_isLattice_390 (coe v2)))
      (coe
         du_'8743''45'distrib'737''45''8744'_438 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Structures.Biased.IsDistributiveLatticeʳʲᵐ.isDistributiveLatticeʳʲᵐ
d_isDistributiveLattice'691''690''7504'_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
d_isDistributiveLattice'691''690''7504'_442 ~v0 ~v1 ~v2 ~v3 v4 v5
                                            v6
  = du_isDistributiveLattice'691''690''7504'_442 v4 v5 v6
du_isDistributiveLattice'691''690''7504'_442 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice'691''690''7504'_380 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
du_isDistributiveLattice'691''690''7504'_442 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_IsDistributiveLattice'46'constructor_41059
      (coe d_isLattice_390 (coe v2))
      (coe du_'8744''45'distrib'45''8743'_436 (coe v0) (coe v1) (coe v2))
      (coe du_'8743''45'distrib'45''8744'_440 (coe v0) (coe v1) (coe v2))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ
d_IsBooleanAlgebra'691'_454 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T_IsBooleanAlgebra'691'_454
  = C_IsBooleanAlgebra'691''46'constructor_9673 MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
                                                (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                                (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ.isDistributiveLattice
d_isDistributiveLattice_474 ::
  T_IsBooleanAlgebra'691'_454 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
d_isDistributiveLattice_474 v0
  = case coe v0 of
      C_IsBooleanAlgebra'691''46'constructor_9673 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ.∨-complementʳ
d_'8744''45'complement'691'_476 ::
  T_IsBooleanAlgebra'691'_454 -> AgdaAny -> AgdaAny
d_'8744''45'complement'691'_476 v0
  = case coe v0 of
      C_IsBooleanAlgebra'691''46'constructor_9673 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ.∧-complementʳ
d_'8743''45'complement'691'_478 ::
  T_IsBooleanAlgebra'691'_454 -> AgdaAny -> AgdaAny
d_'8743''45'complement'691'_478 v0
  = case coe v0 of
      C_IsBooleanAlgebra'691''46'constructor_9673 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ.¬-cong
d_'172''45'cong_480 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'cong_480 v0
  = case coe v0 of
      C_IsBooleanAlgebra'691''46'constructor_9673 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.absorptive
d_absorptive_484 ::
  T_IsBooleanAlgebra'691'_454 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_484 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3020
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe d_isDistributiveLattice_474 (coe v0)))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.isEquivalence
d_isEquivalence_486 ::
  T_IsBooleanAlgebra'691'_454 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_486 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe d_isDistributiveLattice_474 (coe v0)))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.isLattice
d_isLattice_488 ::
  T_IsBooleanAlgebra'691'_454 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
d_isLattice_488 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
      (coe d_isDistributiveLattice_474 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.isPartialEquivalence
d_isPartialEquivalence_490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_isPartialEquivalence_490 v9
du_isPartialEquivalence_490 ::
  T_IsBooleanAlgebra'691'_454 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_490 v0
  = let v1 = d_isDistributiveLattice_474 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
               (coe v2))))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.refl
d_refl_492 :: T_IsBooleanAlgebra'691'_454 -> AgdaAny -> AgdaAny
d_refl_492 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
            (coe d_isDistributiveLattice_474 (coe v0))))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.reflexive
d_reflexive_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_494 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_reflexive_494 v9
du_reflexive_494 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_494 v0
  = let v1 = d_isDistributiveLattice_474 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
                 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                 (coe v2))
              v3))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.sym
d_sym_496 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_496 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
            (coe d_isDistributiveLattice_474 (coe v0))))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.trans
d_trans_498 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_498 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
            (coe d_isDistributiveLattice_474 (coe v0))))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_500 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 v9
  = du_'8743''45'absorbs'45''8744'_500 v9
du_'8743''45'absorbs'45''8744'_500 ::
  T_IsBooleanAlgebra'691'_454 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_500 v0
  = let v1 = d_isDistributiveLattice_474 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3036
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v1)))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∧-assoc
d_'8743''45'assoc_502 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_502 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3016
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe d_isDistributiveLattice_474 (coe v0)))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∧-comm
d_'8743''45'comm_504 ::
  T_IsBooleanAlgebra'691'_454 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_504 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3014
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe d_isDistributiveLattice_474 (coe v0)))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∧-cong
d_'8743''45'cong_506 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_506 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3018
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe d_isDistributiveLattice_474 (coe v0)))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∧-congʳ
d_'8743''45'cong'691'_508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'691'_508 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8743''45'cong'691'_508 v9
du_'8743''45'cong'691'_508 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'691'_508 v0
  = let v1 = d_isDistributiveLattice_474 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3042
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v1)))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∧-congˡ
d_'8743''45'cong'737'_510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'737'_510 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8743''45'cong'737'_510 v9
du_'8743''45'cong'737'_510 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'737'_510 v0
  = let v1 = d_isDistributiveLattice_474 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3038
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v1)))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∧-distrib-∨
d_'8743''45'distrib'45''8744'_512 ::
  T_IsBooleanAlgebra'691'_454 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_512 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3074
      (coe d_isDistributiveLattice_474 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∧-distribʳ-∨
d_'8743''45'distrib'691''45''8744'_514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'691''45''8744'_514 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 v9
  = du_'8743''45'distrib'691''45''8744'_514 v9
du_'8743''45'distrib'691''45''8744'_514 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'691''45''8744'_514 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'691''45''8744'_3122
      (coe d_isDistributiveLattice_474 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8744'_516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 v9
  = du_'8743''45'distrib'737''45''8744'_516 v9
du_'8743''45'distrib'737''45''8744'_516 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'737''45''8744'_516 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3120
      (coe d_isDistributiveLattice_474 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  ~v8 v9
  = du_'8744''45'absorbs'45''8743'_518 v9
du_'8744''45'absorbs'45''8743'_518 ::
  T_IsBooleanAlgebra'691'_454 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_518 v0
  = let v1 = d_isDistributiveLattice_474 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3034
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v1)))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∨-assoc
d_'8744''45'assoc_520 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_520 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3010
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe d_isDistributiveLattice_474 (coe v0)))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∨-comm
d_'8744''45'comm_522 ::
  T_IsBooleanAlgebra'691'_454 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_522 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3008
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe d_isDistributiveLattice_474 (coe v0)))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∨-cong
d_'8744''45'cong_524 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_524 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3012
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe d_isDistributiveLattice_474 (coe v0)))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∨-congʳ
d_'8744''45'cong'691'_526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'691'_526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8744''45'cong'691'_526 v9
du_'8744''45'cong'691'_526 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'691'_526 v0
  = let v1 = d_isDistributiveLattice_474 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3050
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v1)))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∨-congˡ
d_'8744''45'cong'737'_528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'737'_528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_'8744''45'cong'737'_528 v9
du_'8744''45'cong'737'_528 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'737'_528 v0
  = let v1 = d_isDistributiveLattice_474 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3046
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070 (coe v1)))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∨-distrib-∧
d_'8744''45'distrib'45''8743'_530 ::
  T_IsBooleanAlgebra'691'_454 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_530 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3072
      (coe d_isDistributiveLattice_474 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'691''45''8743'_532 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 v9
  = du_'8744''45'distrib'691''45''8743'_532 v9
du_'8744''45'distrib'691''45''8743'_532 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'691''45''8743'_532 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3118
      (coe d_isDistributiveLattice_474 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ._.∨-distribˡ-∧
d_'8744''45'distrib'737''45''8743'_534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'737''45''8743'_534 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 ~v8 v9
  = du_'8744''45'distrib'737''45''8743'_534 v9
du_'8744''45'distrib'737''45''8743'_534 ::
  T_IsBooleanAlgebra'691'_454 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'737''45''8743'_534 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'737''45''8743'_3116
      (coe d_isDistributiveLattice_474 (coe v0))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ.setoid
d_setoid_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_536 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_setoid_536 v9
du_setoid_536 ::
  T_IsBooleanAlgebra'691'_454 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_536 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_761
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
            (coe d_isDistributiveLattice_474 (coe v0))))
-- Algebra.Lattice.Structures.Biased.IsBooleanAlgebraʳ.isBooleanAlgebraʳ
d_isBooleanAlgebra'691'_538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3134
d_isBooleanAlgebra'691'_538 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_isBooleanAlgebra'691'_538 v4 v5 v6 v7 v8 v9
du_isBooleanAlgebra'691'_538 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra'691'_454 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3134
du_isBooleanAlgebra'691'_538 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_IsBooleanAlgebra'46'constructor_44131
      (coe d_isDistributiveLattice_474 (coe v5))
      (coe
         MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'inv'691''8658'inv_456
         (coe du_setoid_536 (coe v5)) (coe v0) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3008
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
               (coe d_isDistributiveLattice_474 (coe v5))))
         (coe d_'8744''45'complement'691'_476 (coe v5)))
      (coe
         MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'inv'691''8658'inv_456
         (coe du_setoid_536 (coe v5)) (coe v1) (coe v2) (coe v4)
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3014
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
               (coe d_isDistributiveLattice_474 (coe v5))))
         (coe d_'8743''45'complement'691'_478 (coe v5)))
      (coe d_'172''45'cong_480 (coe v5))
