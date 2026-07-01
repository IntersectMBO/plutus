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

module MAlonzo.Code.Relation.Binary.Lattice.Structures where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Relation.Binary.Lattice.Structures.IsJoinSemilattice
d_IsJoinSemilattice_22 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsJoinSemilattice_22
  = C_constructor_112 MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
                      (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice.isPartialOrder
d_isPartialOrder_30 ::
  T_IsJoinSemilattice_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_30 v0
  = case coe v0 of
      C_constructor_112 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice.supremum
d_supremum_32 ::
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_32 v0
  = case coe v0 of
      C_constructor_112 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice.x≤x∨y
d_x'8804'x'8744'y_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsJoinSemilattice_22 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_38 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_x'8804'x'8744'y_38 v7 v8 v9
du_x'8804'x'8744'y_38 ::
  T_IsJoinSemilattice_22 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_38 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_supremum_32 v0 v1 v2)
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice.y≤x∨y
d_y'8804'x'8744'y_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsJoinSemilattice_22 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_50 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_y'8804'x'8744'y_50 v7 v8 v9
du_y'8804'x'8744'y_50 ::
  T_IsJoinSemilattice_22 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_50 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe d_supremum_32 v0 v1 v2))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice.∨-least
d_'8744''45'least_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_64 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_'8744''45'least_64 v7 v8 v9 v10
du_'8744''45'least_64 ::
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_64 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe d_supremum_32 v0 v1 v2))
      v3
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.antisym
d_antisym_76 ::
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_76 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe d_isPartialOrder_30 (coe v0))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.isEquivalence
d_isEquivalence_78 ::
  T_IsJoinSemilattice_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_78 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_30 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.isPreorder
d_isPreorder_80 ::
  T_IsJoinSemilattice_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_80 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe d_isPartialOrder_30 (coe v0))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.refl
d_refl_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsJoinSemilattice_22 -> AgdaAny -> AgdaAny
d_refl_82 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_refl_82 v7
du_refl_82 :: T_IsJoinSemilattice_22 -> AgdaAny -> AgdaAny
du_refl_82 v0
  = let v1 = d_isPartialOrder_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_104
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.reflexive
d_reflexive_84 ::
  T_IsJoinSemilattice_22 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_84 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_30 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.trans
d_trans_86 ::
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_86 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_30 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsJoinSemilattice_22 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_88 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8764''45'resp'45''8776'_88 v7
du_'8764''45'resp'45''8776'_88 ::
  T_IsJoinSemilattice_22 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_88 v0
  = let v1 = d_isPartialOrder_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8764''45'resp'691''45''8776'_90 v7
du_'8764''45'resp'691''45''8776'_90 ::
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_90 v0
  = let v1 = d_isPartialOrder_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_92 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8764''45'resp'737''45''8776'_92 v7
du_'8764''45'resp'737''45''8776'_92 ::
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_92 v0
  = let v1 = d_isPartialOrder_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsJoinSemilattice_22 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8818''45'resp'45''8776'_94 v7
du_'8818''45'resp'45''8776'_94 ::
  T_IsJoinSemilattice_22 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_94 v0
  = let v1 = d_isPartialOrder_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_96 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8818''45'resp'691''45''8776'_96 v7
du_'8818''45'resp'691''45''8776'_96 ::
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_96 v0
  = let v1 = d_isPartialOrder_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_98 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8818''45'resp'737''45''8776'_98 v7
du_'8818''45'resp'737''45''8776'_98 ::
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_98 v0
  = let v1 = d_isPartialOrder_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsJoinSemilattice_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_102 v7
du_isPartialEquivalence_102 ::
  T_IsJoinSemilattice_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_102 v0
  = let v1 = d_isPartialOrder_30 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.Eq.refl
d_refl_104 :: T_IsJoinSemilattice_22 -> AgdaAny -> AgdaAny
d_refl_104 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_30 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.Eq.reflexive
d_reflexive_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsJoinSemilattice_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_106 v7
du_reflexive_106 ::
  T_IsJoinSemilattice_22 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_106 v0
  = let v1 = d_isPartialOrder_30 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                 (coe v2))
              v3))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.Eq.sym
d_sym_108 ::
  T_IsJoinSemilattice_22 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_108 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_30 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.Eq.trans
d_trans_110 ::
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_110 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_30 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice
d_IsBoundedJoinSemilattice_118 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsBoundedJoinSemilattice_118
  = C_constructor_180 T_IsJoinSemilattice_22 (AgdaAny -> AgdaAny)
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice.isJoinSemilattice
d_isJoinSemilattice_128 ::
  T_IsBoundedJoinSemilattice_118 -> T_IsJoinSemilattice_22
d_isJoinSemilattice_128 v0
  = case coe v0 of
      C_constructor_180 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice.minimum
d_minimum_130 ::
  T_IsBoundedJoinSemilattice_118 -> AgdaAny -> AgdaAny
d_minimum_130 v0
  = case coe v0 of
      C_constructor_180 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.antisym
d_antisym_134 ::
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_134 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_128 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.isEquivalence
d_isEquivalence_136 ::
  T_IsBoundedJoinSemilattice_118 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_136 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_128 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.isPartialOrder
d_isPartialOrder_138 ::
  T_IsBoundedJoinSemilattice_118 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_138 v0
  = coe d_isPartialOrder_30 (coe d_isJoinSemilattice_128 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.isPreorder
d_isPreorder_140 ::
  T_IsBoundedJoinSemilattice_118 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_140 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_128 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.refl
d_refl_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsBoundedJoinSemilattice_118 -> AgdaAny -> AgdaAny
d_refl_142 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_142 v8
du_refl_142 :: T_IsBoundedJoinSemilattice_118 -> AgdaAny -> AgdaAny
du_refl_142 v0
  = let v1 = d_isJoinSemilattice_128 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.reflexive
d_reflexive_144 ::
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_144 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_128 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.supremum
d_supremum_146 ::
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_146 v0
  = coe d_supremum_32 (coe d_isJoinSemilattice_128 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.trans
d_trans_148 ::
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_148 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_128 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.x≤x∨y
d_x'8804'x'8744'y_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_118 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8804'x'8744'y_150 v8
du_x'8804'x'8744'y_150 ::
  T_IsBoundedJoinSemilattice_118 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_150 v0
  = coe du_x'8804'x'8744'y_38 (coe d_isJoinSemilattice_128 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.y≤x∨y
d_y'8804'x'8744'y_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_118 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_y'8804'x'8744'y_152 v8
du_y'8804'x'8744'y_152 ::
  T_IsBoundedJoinSemilattice_118 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_152 v0
  = coe du_y'8804'x'8744'y_50 (coe d_isJoinSemilattice_128 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.∨-least
d_'8744''45'least_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8744''45'least_154 v8
du_'8744''45'least_154 ::
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_154 v0
  = coe du_'8744''45'least_64 (coe d_isJoinSemilattice_128 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8764''45'resp'45''8776'_156 v8
du_'8764''45'resp'45''8776'_156 ::
  T_IsBoundedJoinSemilattice_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_156 v0
  = let v1 = d_isJoinSemilattice_128 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'691''45''8776'_158 v8
du_'8764''45'resp'691''45''8776'_158 ::
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_158 v0
  = let v1 = d_isJoinSemilattice_128 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'737''45''8776'_160 v8
du_'8764''45'resp'737''45''8776'_160 ::
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_160 v0
  = let v1 = d_isJoinSemilattice_128 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8818''45'resp'45''8776'_162 v8
du_'8818''45'resp'45''8776'_162 ::
  T_IsBoundedJoinSemilattice_118 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_162 v0
  = let v1 = d_isJoinSemilattice_128 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'691''45''8776'_164 v8
du_'8818''45'resp'691''45''8776'_164 ::
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_164 v0
  = let v1 = d_isJoinSemilattice_128 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'737''45''8776'_166 v8
du_'8818''45'resp'737''45''8776'_166 ::
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_166 v0
  = let v1 = d_isJoinSemilattice_128 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_118 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_170 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_170 v8
du_isPartialEquivalence_170 ::
  T_IsBoundedJoinSemilattice_118 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_170 v0
  = let v1 = d_isJoinSemilattice_128 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.Eq.refl
d_refl_172 :: T_IsBoundedJoinSemilattice_118 -> AgdaAny -> AgdaAny
d_refl_172 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_128 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.Eq.reflexive
d_reflexive_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_174 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_174 v8
du_reflexive_174 ::
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_174 v0
  = let v1 = d_isJoinSemilattice_128 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                    (coe v3))
                 v4)))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.Eq.sym
d_sym_176 ::
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_176 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_128 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.Eq.trans
d_trans_178 ::
  T_IsBoundedJoinSemilattice_118 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_178 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_128 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice
d_IsMeetSemilattice_184 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMeetSemilattice_184
  = C_constructor_274 MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
                      (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice.isPartialOrder
d_isPartialOrder_192 ::
  T_IsMeetSemilattice_184 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_192 v0
  = case coe v0 of
      C_constructor_274 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice.infimum
d_infimum_194 ::
  T_IsMeetSemilattice_184 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_194 v0
  = case coe v0 of
      C_constructor_274 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice.x∧y≤x
d_x'8743'y'8804'x_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_184 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_x'8743'y'8804'x_200 v7 v8 v9
du_x'8743'y'8804'x_200 ::
  T_IsMeetSemilattice_184 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_200 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_infimum_194 v0 v1 v2)
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice.x∧y≤y
d_x'8743'y'8804'y_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_184 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_x'8743'y'8804'y_212 v7 v8 v9
du_x'8743'y'8804'y_212 ::
  T_IsMeetSemilattice_184 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_212 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe d_infimum_194 v0 v1 v2))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice.∧-greatest
d_'8743''45'greatest_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_'8743''45'greatest_226 v7 v8 v9 v10
du_'8743''45'greatest_226 ::
  T_IsMeetSemilattice_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_226 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe d_infimum_194 v0 v2 v3))
      v1
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.antisym
d_antisym_238 ::
  T_IsMeetSemilattice_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_238 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe d_isPartialOrder_192 (coe v0))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.isEquivalence
d_isEquivalence_240 ::
  T_IsMeetSemilattice_184 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_240 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_192 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.isPreorder
d_isPreorder_242 ::
  T_IsMeetSemilattice_184 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_242 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe d_isPartialOrder_192 (coe v0))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.refl
d_refl_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_184 -> AgdaAny -> AgdaAny
d_refl_244 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_refl_244 v7
du_refl_244 :: T_IsMeetSemilattice_184 -> AgdaAny -> AgdaAny
du_refl_244 v0
  = let v1 = d_isPartialOrder_192 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_104
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.reflexive
d_reflexive_246 ::
  T_IsMeetSemilattice_184 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_246 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_192 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.trans
d_trans_248 ::
  T_IsMeetSemilattice_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_248 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_192 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_184 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8764''45'resp'45''8776'_250 v7
du_'8764''45'resp'45''8776'_250 ::
  T_IsMeetSemilattice_184 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_250 v0
  = let v1 = d_isPartialOrder_192 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8764''45'resp'691''45''8776'_252 v7
du_'8764''45'resp'691''45''8776'_252 ::
  T_IsMeetSemilattice_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_252 v0
  = let v1 = d_isPartialOrder_192 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8764''45'resp'737''45''8776'_254 v7
du_'8764''45'resp'737''45''8776'_254 ::
  T_IsMeetSemilattice_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_254 v0
  = let v1 = d_isPartialOrder_192 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_184 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8818''45'resp'45''8776'_256 v7
du_'8818''45'resp'45''8776'_256 ::
  T_IsMeetSemilattice_184 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_256 v0
  = let v1 = d_isPartialOrder_192 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_258 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8818''45'resp'691''45''8776'_258 v7
du_'8818''45'resp'691''45''8776'_258 ::
  T_IsMeetSemilattice_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_258 v0
  = let v1 = d_isPartialOrder_192 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8818''45'resp'737''45''8776'_260 v7
du_'8818''45'resp'737''45''8776'_260 ::
  T_IsMeetSemilattice_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_260 v0
  = let v1 = d_isPartialOrder_192 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_184 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_264 v7
du_isPartialEquivalence_264 ::
  T_IsMeetSemilattice_184 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_264 v0
  = let v1 = d_isPartialOrder_192 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.Eq.refl
d_refl_266 :: T_IsMeetSemilattice_184 -> AgdaAny -> AgdaAny
d_refl_266 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_192 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.Eq.reflexive
d_reflexive_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_184 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_268 v7
du_reflexive_268 ::
  T_IsMeetSemilattice_184 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_268 v0
  = let v1 = d_isPartialOrder_192 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                 (coe v2))
              v3))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.Eq.sym
d_sym_270 ::
  T_IsMeetSemilattice_184 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_270 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_192 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.Eq.trans
d_trans_272 ::
  T_IsMeetSemilattice_184 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_272 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_192 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice
d_IsBoundedMeetSemilattice_280 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsBoundedMeetSemilattice_280
  = C_constructor_342 T_IsMeetSemilattice_184 (AgdaAny -> AgdaAny)
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice.isMeetSemilattice
d_isMeetSemilattice_290 ::
  T_IsBoundedMeetSemilattice_280 -> T_IsMeetSemilattice_184
d_isMeetSemilattice_290 v0
  = case coe v0 of
      C_constructor_342 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice.maximum
d_maximum_292 ::
  T_IsBoundedMeetSemilattice_280 -> AgdaAny -> AgdaAny
d_maximum_292 v0
  = case coe v0 of
      C_constructor_342 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.antisym
d_antisym_296 ::
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_296 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe d_isPartialOrder_192 (coe d_isMeetSemilattice_290 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.infimum
d_infimum_298 ::
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_298 v0
  = coe d_infimum_194 (coe d_isMeetSemilattice_290 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.isEquivalence
d_isEquivalence_300 ::
  T_IsBoundedMeetSemilattice_280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_300 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_192 (coe d_isMeetSemilattice_290 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.isPartialOrder
d_isPartialOrder_302 ::
  T_IsBoundedMeetSemilattice_280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_302 v0
  = coe d_isPartialOrder_192 (coe d_isMeetSemilattice_290 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.isPreorder
d_isPreorder_304 ::
  T_IsBoundedMeetSemilattice_280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_304 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe d_isPartialOrder_192 (coe d_isMeetSemilattice_290 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.refl
d_refl_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsBoundedMeetSemilattice_280 -> AgdaAny -> AgdaAny
d_refl_306 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_306 v8
du_refl_306 :: T_IsBoundedMeetSemilattice_280 -> AgdaAny -> AgdaAny
du_refl_306 v0
  = let v1 = d_isMeetSemilattice_290 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_192 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.reflexive
d_reflexive_308 ::
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_308 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_192 (coe d_isMeetSemilattice_290 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.trans
d_trans_310 ::
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_310 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_192 (coe d_isMeetSemilattice_290 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.x∧y≤x
d_x'8743'y'8804'x_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_280 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8743'y'8804'x_312 v8
du_x'8743'y'8804'x_312 ::
  T_IsBoundedMeetSemilattice_280 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_312 v0
  = coe du_x'8743'y'8804'x_200 (coe d_isMeetSemilattice_290 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.x∧y≤y
d_x'8743'y'8804'y_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_280 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8743'y'8804'y_314 v8
du_x'8743'y'8804'y_314 ::
  T_IsBoundedMeetSemilattice_280 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_314 v0
  = coe du_x'8743'y'8804'y_212 (coe d_isMeetSemilattice_290 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.∧-greatest
d_'8743''45'greatest_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8743''45'greatest_316 v8
du_'8743''45'greatest_316 ::
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_316 v0
  = coe
      du_'8743''45'greatest_226 (coe d_isMeetSemilattice_290 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_280 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_318 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8764''45'resp'45''8776'_318 v8
du_'8764''45'resp'45''8776'_318 ::
  T_IsBoundedMeetSemilattice_280 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_318 v0
  = let v1 = d_isMeetSemilattice_290 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_192 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_320 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'691''45''8776'_320 v8
du_'8764''45'resp'691''45''8776'_320 ::
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_320 v0
  = let v1 = d_isMeetSemilattice_290 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_192 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'737''45''8776'_322 v8
du_'8764''45'resp'737''45''8776'_322 ::
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_322 v0
  = let v1 = d_isMeetSemilattice_290 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_192 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_280 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8818''45'resp'45''8776'_324 v8
du_'8818''45'resp'45''8776'_324 ::
  T_IsBoundedMeetSemilattice_280 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_324 v0
  = let v1 = d_isMeetSemilattice_290 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_192 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'691''45''8776'_326 v8
du_'8818''45'resp'691''45''8776'_326 ::
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_326 v0
  = let v1 = d_isMeetSemilattice_290 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_192 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'737''45''8776'_328 v8
du_'8818''45'resp'737''45''8776'_328 ::
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_328 v0
  = let v1 = d_isMeetSemilattice_290 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_192 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_332 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_332 v8
du_isPartialEquivalence_332 ::
  T_IsBoundedMeetSemilattice_280 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_332 v0
  = let v1 = d_isMeetSemilattice_290 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_192 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.Eq.refl
d_refl_334 :: T_IsBoundedMeetSemilattice_280 -> AgdaAny -> AgdaAny
d_refl_334 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_192 (coe d_isMeetSemilattice_290 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.Eq.reflexive
d_reflexive_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_336 v8
du_reflexive_336 ::
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_336 v0
  = let v1 = d_isMeetSemilattice_290 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_192 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                    (coe v3))
                 v4)))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.Eq.sym
d_sym_338 ::
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_338 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_192 (coe d_isMeetSemilattice_290 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.Eq.trans
d_trans_340 ::
  T_IsBoundedMeetSemilattice_280 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_340 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_192 (coe d_isMeetSemilattice_290 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsLattice
d_IsLattice_348 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsLattice_348
  = C_constructor_424 MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
                      (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                      (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Relation.Binary.Lattice.Structures.IsLattice.isPartialOrder
d_isPartialOrder_360 ::
  T_IsLattice_348 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_360 v0
  = case coe v0 of
      C_constructor_424 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsLattice.supremum
d_supremum_362 ::
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_362 v0
  = case coe v0 of
      C_constructor_424 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsLattice.infimum
d_infimum_364 ::
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_364 v0
  = case coe v0 of
      C_constructor_424 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsLattice.isJoinSemilattice
d_isJoinSemilattice_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 -> T_IsJoinSemilattice_22
d_isJoinSemilattice_366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isJoinSemilattice_366 v8
du_isJoinSemilattice_366 ::
  T_IsLattice_348 -> T_IsJoinSemilattice_22
du_isJoinSemilattice_366 v0
  = coe
      C_constructor_112 (coe d_isPartialOrder_360 (coe v0))
      (coe d_supremum_362 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice.isMeetSemilattice
d_isMeetSemilattice_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 -> T_IsMeetSemilattice_184
d_isMeetSemilattice_368 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isMeetSemilattice_368 v8
du_isMeetSemilattice_368 ::
  T_IsLattice_348 -> T_IsMeetSemilattice_184
du_isMeetSemilattice_368 v0
  = coe
      C_constructor_274 (coe d_isPartialOrder_360 (coe v0))
      (coe d_infimum_364 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.x≤x∨y
d_x'8804'x'8744'y_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_372 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8804'x'8744'y_372 v8
du_x'8804'x'8744'y_372 ::
  T_IsLattice_348 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_372 v0
  = coe du_x'8804'x'8744'y_38 (coe du_isJoinSemilattice_366 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.y≤x∨y
d_y'8804'x'8744'y_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_374 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_y'8804'x'8744'y_374 v8
du_y'8804'x'8744'y_374 ::
  T_IsLattice_348 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_374 v0
  = coe du_y'8804'x'8744'y_50 (coe du_isJoinSemilattice_366 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.∨-least
d_'8744''45'least_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_376 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8744''45'least_376 v8
du_'8744''45'least_376 ::
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_376 v0
  = coe du_'8744''45'least_64 (coe du_isJoinSemilattice_366 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.x∧y≤x
d_x'8743'y'8804'x_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8743'y'8804'x_380 v8
du_x'8743'y'8804'x_380 ::
  T_IsLattice_348 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_380 v0
  = coe
      du_x'8743'y'8804'x_200 (coe du_isMeetSemilattice_368 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.x∧y≤y
d_x'8743'y'8804'y_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8743'y'8804'y_382 v8
du_x'8743'y'8804'y_382 ::
  T_IsLattice_348 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_382 v0
  = coe
      du_x'8743'y'8804'y_212 (coe du_isMeetSemilattice_368 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.∧-greatest
d_'8743''45'greatest_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_384 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8743''45'greatest_384 v8
du_'8743''45'greatest_384 ::
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_384 v0
  = coe
      du_'8743''45'greatest_226 (coe du_isMeetSemilattice_368 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.antisym
d_antisym_388 ::
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_388 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe d_isPartialOrder_360 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.isEquivalence
d_isEquivalence_390 ::
  T_IsLattice_348 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_390 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_360 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsLattice._.isPreorder
d_isPreorder_392 ::
  T_IsLattice_348 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_392 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe d_isPartialOrder_360 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.refl
d_refl_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 -> AgdaAny -> AgdaAny
d_refl_394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_394 v8
du_refl_394 :: T_IsLattice_348 -> AgdaAny -> AgdaAny
du_refl_394 v0
  = let v1 = d_isPartialOrder_360 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_104
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsLattice._.reflexive
d_reflexive_396 ::
  T_IsLattice_348 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_396 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_360 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsLattice._.trans
d_trans_398 ::
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_398 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_360 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsLattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_400 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8764''45'resp'45''8776'_400 v8
du_'8764''45'resp'45''8776'_400 ::
  T_IsLattice_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_400 v0
  = let v1 = d_isPartialOrder_360 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsLattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_402 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'691''45''8776'_402 v8
du_'8764''45'resp'691''45''8776'_402 ::
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_402 v0
  = let v1 = d_isPartialOrder_360 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsLattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_404 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'737''45''8776'_404 v8
du_'8764''45'resp'737''45''8776'_404 ::
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_404 v0
  = let v1 = d_isPartialOrder_360 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsLattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8818''45'resp'45''8776'_406 v8
du_'8818''45'resp'45''8776'_406 ::
  T_IsLattice_348 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_406 v0
  = let v1 = d_isPartialOrder_360 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsLattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_408 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'691''45''8776'_408 v8
du_'8818''45'resp'691''45''8776'_408 ::
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_408 v0
  = let v1 = d_isPartialOrder_360 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsLattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_410 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'737''45''8776'_410 v8
du_'8818''45'resp'737''45''8776'_410 ::
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_410 v0
  = let v1 = d_isPartialOrder_360 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsLattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_414 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_414 v8
du_isPartialEquivalence_414 ::
  T_IsLattice_348 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_414 v0
  = let v1 = d_isPartialOrder_360 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsLattice._.Eq.refl
d_refl_416 :: T_IsLattice_348 -> AgdaAny -> AgdaAny
d_refl_416 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_360 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsLattice._.Eq.reflexive
d_reflexive_418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_348 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_418 v8
du_reflexive_418 ::
  T_IsLattice_348 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_418 v0
  = let v1 = d_isPartialOrder_360 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                 (coe v2))
              v3))
-- Relation.Binary.Lattice.Structures.IsLattice._.Eq.sym
d_sym_420 ::
  T_IsLattice_348 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_420 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_360 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsLattice._.Eq.trans
d_trans_422 ::
  T_IsLattice_348 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_422 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_360 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice
d_IsDistributiveLattice_430 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsDistributiveLattice_430
  = C_constructor_504 T_IsLattice_348
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice.isLattice
d_isLattice_440 :: T_IsDistributiveLattice_430 -> T_IsLattice_348
d_isLattice_440 v0
  = case coe v0 of
      C_constructor_504 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_442 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8744'_442 v0
  = case coe v0 of
      C_constructor_504 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.antisym
d_antisym_446 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_446 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe d_isPartialOrder_360 (coe d_isLattice_440 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.infimum
d_infimum_448 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_448 v0 = coe d_infimum_364 (coe d_isLattice_440 (coe v0))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.isEquivalence
d_isEquivalence_450 ::
  T_IsDistributiveLattice_430 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_450 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_360 (coe d_isLattice_440 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.isJoinSemilattice
d_isJoinSemilattice_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 -> T_IsJoinSemilattice_22
d_isJoinSemilattice_452 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isJoinSemilattice_452 v8
du_isJoinSemilattice_452 ::
  T_IsDistributiveLattice_430 -> T_IsJoinSemilattice_22
du_isJoinSemilattice_452 v0
  = coe du_isJoinSemilattice_366 (coe d_isLattice_440 (coe v0))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.isMeetSemilattice
d_isMeetSemilattice_454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 -> T_IsMeetSemilattice_184
d_isMeetSemilattice_454 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isMeetSemilattice_454 v8
du_isMeetSemilattice_454 ::
  T_IsDistributiveLattice_430 -> T_IsMeetSemilattice_184
du_isMeetSemilattice_454 v0
  = coe du_isMeetSemilattice_368 (coe d_isLattice_440 (coe v0))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.isPartialOrder
d_isPartialOrder_456 ::
  T_IsDistributiveLattice_430 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_456 v0
  = coe d_isPartialOrder_360 (coe d_isLattice_440 (coe v0))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.isPreorder
d_isPreorder_458 ::
  T_IsDistributiveLattice_430 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_458 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe d_isPartialOrder_360 (coe d_isLattice_440 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.refl
d_refl_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 -> AgdaAny -> AgdaAny
d_refl_460 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_460 v8
du_refl_460 :: T_IsDistributiveLattice_430 -> AgdaAny -> AgdaAny
du_refl_460 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.reflexive
d_reflexive_462 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_462 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_360 (coe d_isLattice_440 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.supremum
d_supremum_464 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_464 v0
  = coe d_supremum_362 (coe d_isLattice_440 (coe v0))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.trans
d_trans_466 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_466 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_360 (coe d_isLattice_440 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.x∧y≤x
d_x'8743'y'8804'x_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8743'y'8804'x_468 v8
du_x'8743'y'8804'x_468 ::
  T_IsDistributiveLattice_430 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_468 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (coe
         du_x'8743'y'8804'x_200 (coe du_isMeetSemilattice_368 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.x∧y≤y
d_x'8743'y'8804'y_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8743'y'8804'y_470 v8
du_x'8743'y'8804'y_470 ::
  T_IsDistributiveLattice_430 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_470 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (coe
         du_x'8743'y'8804'y_212 (coe du_isMeetSemilattice_368 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.x≤x∨y
d_x'8804'x'8744'y_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8804'x'8744'y_472 v8
du_x'8804'x'8744'y_472 ::
  T_IsDistributiveLattice_430 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_472 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (coe du_x'8804'x'8744'y_38 (coe du_isJoinSemilattice_366 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.y≤x∨y
d_y'8804'x'8744'y_474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_474 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_y'8804'x'8744'y_474 v8
du_y'8804'x'8744'y_474 ::
  T_IsDistributiveLattice_430 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_474 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (coe du_y'8804'x'8744'y_50 (coe du_isJoinSemilattice_366 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.∧-greatest
d_'8743''45'greatest_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_476 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8743''45'greatest_476 v8
du_'8743''45'greatest_476 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_476 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (coe
         du_'8743''45'greatest_226 (coe du_isMeetSemilattice_368 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.∨-least
d_'8744''45'least_478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_478 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8744''45'least_478 v8
du_'8744''45'least_478 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_478 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (coe du_'8744''45'least_64 (coe du_isJoinSemilattice_366 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_480 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8764''45'resp'45''8776'_480 v8
du_'8764''45'resp'45''8776'_480 ::
  T_IsDistributiveLattice_430 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_480 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_482 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'691''45''8776'_482 v8
du_'8764''45'resp'691''45''8776'_482 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_482 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'737''45''8776'_484 v8
du_'8764''45'resp'737''45''8776'_484 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_484 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_486 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8818''45'resp'45''8776'_486 v8
du_'8818''45'resp'45''8776'_486 ::
  T_IsDistributiveLattice_430 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_486 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_488 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'691''45''8776'_488 v8
du_'8818''45'resp'691''45''8776'_488 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_488 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_490 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'737''45''8776'_490 v8
du_'8818''45'resp'737''45''8776'_490 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_490 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_494 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_494 v8
du_isPartialEquivalence_494 ::
  T_IsDistributiveLattice_430 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_494 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.Eq.refl
d_refl_496 :: T_IsDistributiveLattice_430 -> AgdaAny -> AgdaAny
d_refl_496 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_360 (coe d_isLattice_440 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.Eq.reflexive
d_reflexive_498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_430 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_498 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_498 v8
du_reflexive_498 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_498 v0
  = let v1 = d_isLattice_440 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                    (coe v3))
                 v4)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.Eq.sym
d_sym_500 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_500 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_360 (coe d_isLattice_440 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.Eq.trans
d_trans_502 ::
  T_IsDistributiveLattice_430 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_502 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_360 (coe d_isLattice_440 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice
d_IsBoundedLattice_514 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IsBoundedLattice_514
  = C_constructor_600 T_IsLattice_348 (AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny)
-- Relation.Binary.Lattice.Structures.IsBoundedLattice.isLattice
d_isLattice_530 :: T_IsBoundedLattice_514 -> T_IsLattice_348
d_isLattice_530 v0
  = case coe v0 of
      C_constructor_600 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBoundedLattice.maximum
d_maximum_532 :: T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny
d_maximum_532 v0
  = case coe v0 of
      C_constructor_600 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBoundedLattice.minimum
d_minimum_534 :: T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny
d_minimum_534 v0
  = case coe v0 of
      C_constructor_600 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.antisym
d_antisym_538 ::
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_538 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe d_isPartialOrder_360 (coe d_isLattice_530 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.infimum
d_infimum_540 ::
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_540 v0 = coe d_infimum_364 (coe d_isLattice_530 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.isEquivalence
d_isEquivalence_542 ::
  T_IsBoundedLattice_514 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_542 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_360 (coe d_isLattice_530 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.isJoinSemilattice
d_isJoinSemilattice_544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_514 -> T_IsJoinSemilattice_22
d_isJoinSemilattice_544 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isJoinSemilattice_544 v10
du_isJoinSemilattice_544 ::
  T_IsBoundedLattice_514 -> T_IsJoinSemilattice_22
du_isJoinSemilattice_544 v0
  = coe du_isJoinSemilattice_366 (coe d_isLattice_530 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.isMeetSemilattice
d_isMeetSemilattice_546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_514 -> T_IsMeetSemilattice_184
d_isMeetSemilattice_546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isMeetSemilattice_546 v10
du_isMeetSemilattice_546 ::
  T_IsBoundedLattice_514 -> T_IsMeetSemilattice_184
du_isMeetSemilattice_546 v0
  = coe du_isMeetSemilattice_368 (coe d_isLattice_530 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.isPartialOrder
d_isPartialOrder_548 ::
  T_IsBoundedLattice_514 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_548 v0
  = coe d_isPartialOrder_360 (coe d_isLattice_530 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.isPreorder
d_isPreorder_550 ::
  T_IsBoundedLattice_514 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_550 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe d_isPartialOrder_360 (coe d_isLattice_530 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.refl
d_refl_552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny
d_refl_552 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_refl_552 v10
du_refl_552 :: T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny
du_refl_552 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.reflexive
d_reflexive_554 ::
  T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_554 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_360 (coe d_isLattice_530 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.supremum
d_supremum_556 ::
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_556 v0
  = coe d_supremum_362 (coe d_isLattice_530 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.trans
d_trans_558 ::
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_558 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe d_isPartialOrder_360 (coe d_isLattice_530 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.x∧y≤x
d_x'8743'y'8804'x_560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_560 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_x'8743'y'8804'x_560 v10
du_x'8743'y'8804'x_560 ::
  T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_560 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (coe
         du_x'8743'y'8804'x_200 (coe du_isMeetSemilattice_368 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.x∧y≤y
d_x'8743'y'8804'y_562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_562 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_x'8743'y'8804'y_562 v10
du_x'8743'y'8804'y_562 ::
  T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_562 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (coe
         du_x'8743'y'8804'y_212 (coe du_isMeetSemilattice_368 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.x≤x∨y
d_x'8804'x'8744'y_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_564 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_x'8804'x'8744'y_564 v10
du_x'8804'x'8744'y_564 ::
  T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_564 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (coe du_x'8804'x'8744'y_38 (coe du_isJoinSemilattice_366 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.y≤x∨y
d_y'8804'x'8744'y_566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_566 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_y'8804'x'8744'y_566 v10
du_y'8804'x'8744'y_566 ::
  T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_566 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (coe du_y'8804'x'8744'y_50 (coe du_isJoinSemilattice_366 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.∧-greatest
d_'8743''45'greatest_568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_568 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         v10
  = du_'8743''45'greatest_568 v10
du_'8743''45'greatest_568 ::
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_568 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (coe
         du_'8743''45'greatest_226 (coe du_isMeetSemilattice_368 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.∨-least
d_'8744''45'least_570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_570 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_'8744''45'least_570 v10
du_'8744''45'least_570 ::
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_570 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (coe du_'8744''45'least_64 (coe du_isJoinSemilattice_366 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBoundedLattice_514 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_572 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 v10
  = du_'8764''45'resp'45''8776'_572 v10
du_'8764''45'resp'45''8776'_572 ::
  T_IsBoundedLattice_514 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_572 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 v10
  = du_'8764''45'resp'691''45''8776'_574 v10
du_'8764''45'resp'691''45''8776'_574 ::
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_574 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_576 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 v10
  = du_'8764''45'resp'737''45''8776'_576 v10
du_'8764''45'resp'737''45''8776'_576 ::
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_576 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBoundedLattice_514 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_578 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 v10
  = du_'8818''45'resp'45''8776'_578 v10
du_'8818''45'resp'45''8776'_578 ::
  T_IsBoundedLattice_514 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_578 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_580 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 v10
  = du_'8818''45'resp'691''45''8776'_580 v10
du_'8818''45'resp'691''45''8776'_580 ::
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_580 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_582 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 v10
  = du_'8818''45'resp'737''45''8776'_582 v10
du_'8818''45'resp'737''45''8776'_582 ::
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_582 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBoundedLattice_514 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           v10
  = du_isPartialEquivalence_586 v10
du_isPartialEquivalence_586 ::
  T_IsBoundedLattice_514 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_586 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.Eq.refl
d_refl_588 :: T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny
d_refl_588 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_360 (coe d_isLattice_530 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.Eq.reflexive
d_reflexive_590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBoundedLattice_514 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_590 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_reflexive_590 v10
du_reflexive_590 ::
  T_IsBoundedLattice_514 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_590 v0
  = let v1 = d_isLattice_530 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_360 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                    (coe v3))
                 v4)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.Eq.sym
d_sym_592 ::
  T_IsBoundedLattice_514 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_592 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_360 (coe d_isLattice_530 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.Eq.trans
d_trans_594 ::
  T_IsBoundedLattice_514 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_594 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe d_isPartialOrder_360 (coe d_isLattice_530 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_596 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_514 -> T_IsBoundedJoinSemilattice_118
d_isBoundedJoinSemilattice_596 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 v10
  = du_isBoundedJoinSemilattice_596 v10
du_isBoundedJoinSemilattice_596 ::
  T_IsBoundedLattice_514 -> T_IsBoundedJoinSemilattice_118
du_isBoundedJoinSemilattice_596 v0
  = coe
      C_constructor_180
      (coe du_isJoinSemilattice_366 (coe d_isLattice_530 (coe v0)))
      (coe d_minimum_534 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_598 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_514 -> T_IsBoundedMeetSemilattice_280
d_isBoundedMeetSemilattice_598 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 v10
  = du_isBoundedMeetSemilattice_598 v10
du_isBoundedMeetSemilattice_598 ::
  T_IsBoundedLattice_514 -> T_IsBoundedMeetSemilattice_280
du_isBoundedMeetSemilattice_598 v0
  = coe
      C_constructor_342
      (coe du_isMeetSemilattice_368 (coe d_isLattice_530 (coe v0)))
      (coe d_maximum_532 (coe v0))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra
d_IsHeytingAlgebra_612 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_IsHeytingAlgebra_612
  = C_constructor_734 T_IsBoundedLattice_514
                      (AgdaAny ->
                       AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra.isBoundedLattice
d_isBoundedLattice_628 ::
  T_IsHeytingAlgebra_612 -> T_IsBoundedLattice_514
d_isBoundedLattice_628 v0
  = case coe v0 of
      C_constructor_734 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra.exponential
d_exponential_630 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exponential_630 v0
  = case coe v0 of
      C_constructor_734 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra.transpose-⇨
d_transpose'45''8680'_638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8680'_638 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11 v12 v13 v14
  = du_transpose'45''8680'_638 v11 v12 v13 v14
du_transpose'45''8680'_638 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8680'_638 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_exponential_630 v0 v1 v2 v3)
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra.transpose-∧
d_transpose'45''8743'_654 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8743'_654 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11 v12 v13 v14
  = du_transpose'45''8743'_654 v11 v12 v13 v14
du_transpose'45''8743'_654 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8743'_654 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_exponential_630 v0 v1 v2 v3)
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.antisym
d_antisym_666 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_666 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         d_isPartialOrder_360
         (coe d_isLattice_530 (coe d_isBoundedLattice_628 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.infimum
d_infimum_668 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_668 v0
  = coe
      d_infimum_364
      (coe d_isLattice_530 (coe d_isBoundedLattice_628 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_670 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingAlgebra_612 -> T_IsBoundedJoinSemilattice_118
d_isBoundedJoinSemilattice_670 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_isBoundedJoinSemilattice_670 v11
du_isBoundedJoinSemilattice_670 ::
  T_IsHeytingAlgebra_612 -> T_IsBoundedJoinSemilattice_118
du_isBoundedJoinSemilattice_670 v0
  = coe
      du_isBoundedJoinSemilattice_596
      (coe d_isBoundedLattice_628 (coe v0))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_672 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingAlgebra_612 -> T_IsBoundedMeetSemilattice_280
d_isBoundedMeetSemilattice_672 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_isBoundedMeetSemilattice_672 v11
du_isBoundedMeetSemilattice_672 ::
  T_IsHeytingAlgebra_612 -> T_IsBoundedMeetSemilattice_280
du_isBoundedMeetSemilattice_672 v0
  = coe
      du_isBoundedMeetSemilattice_598
      (coe d_isBoundedLattice_628 (coe v0))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isEquivalence
d_isEquivalence_674 ::
  T_IsHeytingAlgebra_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_674 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_360
            (coe d_isLattice_530 (coe d_isBoundedLattice_628 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isJoinSemilattice
d_isJoinSemilattice_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingAlgebra_612 -> T_IsJoinSemilattice_22
d_isJoinSemilattice_676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 v11
  = du_isJoinSemilattice_676 v11
du_isJoinSemilattice_676 ::
  T_IsHeytingAlgebra_612 -> T_IsJoinSemilattice_22
du_isJoinSemilattice_676 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe (coe du_isJoinSemilattice_366 (coe d_isLattice_530 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isLattice
d_isLattice_678 :: T_IsHeytingAlgebra_612 -> T_IsLattice_348
d_isLattice_678 v0
  = coe d_isLattice_530 (coe d_isBoundedLattice_628 (coe v0))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isMeetSemilattice
d_isMeetSemilattice_680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingAlgebra_612 -> T_IsMeetSemilattice_184
d_isMeetSemilattice_680 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 v11
  = du_isMeetSemilattice_680 v11
du_isMeetSemilattice_680 ::
  T_IsHeytingAlgebra_612 -> T_IsMeetSemilattice_184
du_isMeetSemilattice_680 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe (coe du_isMeetSemilattice_368 (coe d_isLattice_530 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isPartialOrder
d_isPartialOrder_682 ::
  T_IsHeytingAlgebra_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_682 v0
  = coe
      d_isPartialOrder_360
      (coe d_isLattice_530 (coe d_isBoundedLattice_628 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isPreorder
d_isPreorder_684 ::
  T_IsHeytingAlgebra_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_684 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         d_isPartialOrder_360
         (coe d_isLattice_530 (coe d_isBoundedLattice_628 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.maximum
d_maximum_686 :: T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny
d_maximum_686 v0
  = coe d_maximum_532 (coe d_isBoundedLattice_628 (coe v0))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.minimum
d_minimum_688 :: T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny
d_minimum_688 v0
  = coe d_minimum_534 (coe d_isBoundedLattice_628 (coe v0))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.refl
d_refl_690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny
d_refl_690 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_refl_690 v11
du_refl_690 :: T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny
du_refl_690 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_360 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_104
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.reflexive
d_reflexive_692 ::
  T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_692 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_360
            (coe d_isLattice_530 (coe d_isBoundedLattice_628 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.supremum
d_supremum_694 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_694 v0
  = coe
      d_supremum_362
      (coe d_isLattice_530 (coe d_isBoundedLattice_628 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.trans
d_trans_696 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_696 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_360
            (coe d_isLattice_530 (coe d_isBoundedLattice_628 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.x∧y≤x
d_x'8743'y'8804'x_698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_x'8743'y'8804'x_698 v11
du_x'8743'y'8804'x_698 ::
  T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_698 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (coe
            du_x'8743'y'8804'x_200 (coe du_isMeetSemilattice_368 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.x∧y≤y
d_x'8743'y'8804'y_700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_700 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_x'8743'y'8804'y_700 v11
du_x'8743'y'8804'y_700 ::
  T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_700 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (coe
            du_x'8743'y'8804'y_212 (coe du_isMeetSemilattice_368 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.x≤x∨y
d_x'8804'x'8744'y_702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_702 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_x'8804'x'8744'y_702 v11
du_x'8804'x'8744'y_702 ::
  T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_702 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (coe
            du_x'8804'x'8744'y_38 (coe du_isJoinSemilattice_366 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.y≤x∨y
d_y'8804'x'8744'y_704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_704 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_y'8804'x'8744'y_704 v11
du_y'8804'x'8744'y_704 ::
  T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_704 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (coe
            du_y'8804'x'8744'y_50 (coe du_isJoinSemilattice_366 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.∧-greatest
d_'8743''45'greatest_706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 v11
  = du_'8743''45'greatest_706 v11
du_'8743''45'greatest_706 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_706 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (coe
            du_'8743''45'greatest_226 (coe du_isMeetSemilattice_368 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.∨-least
d_'8744''45'least_708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_708 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_'8744''45'least_708 v11
du_'8744''45'least_708 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_708 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (coe
            du_'8744''45'least_64 (coe du_isJoinSemilattice_366 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.∼-resp-≈
d_'8764''45'resp'45''8776'_710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingAlgebra_612 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_710 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_'8764''45'resp'45''8776'_710 v11
du_'8764''45'resp'45''8776'_710 ::
  T_IsHeytingAlgebra_612 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_710 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_360 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_712 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8764''45'resp'691''45''8776'_712 v11
du_'8764''45'resp'691''45''8776'_712 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_712 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_360 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8764''45'resp'737''45''8776'_714 v11
du_'8764''45'resp'737''45''8776'_714 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_714 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_360 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.≲-resp-≈
d_'8818''45'resp'45''8776'_716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingAlgebra_612 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_716 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_'8818''45'resp'45''8776'_716 v11
du_'8818''45'resp'45''8776'_716 ::
  T_IsHeytingAlgebra_612 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_716 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_360 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_718 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_718 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8818''45'resp'691''45''8776'_718 v11
du_'8818''45'resp'691''45''8776'_718 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_718 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_360 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_720 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8818''45'resp'737''45''8776'_720 v11
du_'8818''45'resp'737''45''8776'_720 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_720 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_360 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.Eq.isPartialEquivalence
d_isPartialEquivalence_724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingAlgebra_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_724 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11
  = du_isPartialEquivalence_724 v11
du_isPartialEquivalence_724 ::
  T_IsHeytingAlgebra_612 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_724 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_360 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.Eq.refl
d_refl_726 :: T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny
d_refl_726 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_360
               (coe d_isLattice_530 (coe d_isBoundedLattice_628 (coe v0))))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.Eq.reflexive
d_reflexive_728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingAlgebra_612 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_728 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_reflexive_728 v11
du_reflexive_728 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_728 v0
  = let v1 = d_isBoundedLattice_628 (coe v0) in
    coe
      (let v2 = d_isLattice_530 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_360 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                       (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                       (coe v4))
                    v5))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.Eq.sym
d_sym_730 ::
  T_IsHeytingAlgebra_612 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_730 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_360
               (coe d_isLattice_530 (coe d_isBoundedLattice_628 (coe v0))))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.Eq.trans
d_trans_732 ::
  T_IsHeytingAlgebra_612 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_732 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_360
               (coe d_isLattice_530 (coe d_isBoundedLattice_628 (coe v0))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra
d_IsBooleanAlgebra_746 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
newtype T_IsBooleanAlgebra_746
  = C_constructor_852 T_IsHeytingAlgebra_612
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._⇨_
d__'8680'__766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8680'__766 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10 ~v11 v12
               v13
  = du__'8680'__766 v6 v8 v12 v13
du__'8680'__766 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'8680'__766 v0 v1 v2 v3 = coe v0 (coe v1 v2) v3
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra.isHeytingAlgebra
d_isHeytingAlgebra_772 ::
  T_IsBooleanAlgebra_746 -> T_IsHeytingAlgebra_612
d_isHeytingAlgebra_772 v0
  = case coe v0 of
      C_constructor_852 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.antisym
d_antisym_776 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_776 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         d_isPartialOrder_360
         (coe
            d_isLattice_530
            (coe
               d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.exponential
d_exponential_778 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exponential_778 v0
  = coe d_exponential_630 (coe d_isHeytingAlgebra_772 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.infimum
d_infimum_780 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_780 v0
  = coe
      d_infimum_364
      (coe
         d_isLattice_530
         (coe d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_782 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBooleanAlgebra_746 -> T_IsBoundedJoinSemilattice_118
d_isBoundedJoinSemilattice_782 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_isBoundedJoinSemilattice_782 v11
du_isBoundedJoinSemilattice_782 ::
  T_IsBooleanAlgebra_746 -> T_IsBoundedJoinSemilattice_118
du_isBoundedJoinSemilattice_782 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (coe
         du_isBoundedJoinSemilattice_596
         (coe d_isBoundedLattice_628 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isBoundedLattice
d_isBoundedLattice_784 ::
  T_IsBooleanAlgebra_746 -> T_IsBoundedLattice_514
d_isBoundedLattice_784 v0
  = coe d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBooleanAlgebra_746 -> T_IsBoundedMeetSemilattice_280
d_isBoundedMeetSemilattice_786 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_isBoundedMeetSemilattice_786 v11
du_isBoundedMeetSemilattice_786 ::
  T_IsBooleanAlgebra_746 -> T_IsBoundedMeetSemilattice_280
du_isBoundedMeetSemilattice_786 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (coe
         du_isBoundedMeetSemilattice_598
         (coe d_isBoundedLattice_628 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isEquivalence
d_isEquivalence_788 ::
  T_IsBooleanAlgebra_746 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_788 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_360
            (coe
               d_isLattice_530
               (coe
                  d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isJoinSemilattice
d_isJoinSemilattice_790 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBooleanAlgebra_746 -> T_IsJoinSemilattice_22
d_isJoinSemilattice_790 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 v11
  = du_isJoinSemilattice_790 v11
du_isJoinSemilattice_790 ::
  T_IsBooleanAlgebra_746 -> T_IsJoinSemilattice_22
du_isJoinSemilattice_790 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe (coe du_isJoinSemilattice_366 (coe d_isLattice_530 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isLattice
d_isLattice_792 :: T_IsBooleanAlgebra_746 -> T_IsLattice_348
d_isLattice_792 v0
  = coe
      d_isLattice_530
      (coe d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isMeetSemilattice
d_isMeetSemilattice_794 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBooleanAlgebra_746 -> T_IsMeetSemilattice_184
d_isMeetSemilattice_794 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 v11
  = du_isMeetSemilattice_794 v11
du_isMeetSemilattice_794 ::
  T_IsBooleanAlgebra_746 -> T_IsMeetSemilattice_184
du_isMeetSemilattice_794 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe (coe du_isMeetSemilattice_368 (coe d_isLattice_530 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isPartialOrder
d_isPartialOrder_796 ::
  T_IsBooleanAlgebra_746 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_796 v0
  = coe
      d_isPartialOrder_360
      (coe
         d_isLattice_530
         (coe d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isPreorder
d_isPreorder_798 ::
  T_IsBooleanAlgebra_746 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_798 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         d_isPartialOrder_360
         (coe
            d_isLattice_530
            (coe
               d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.maximum
d_maximum_800 :: T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny
d_maximum_800 v0
  = coe
      d_maximum_532
      (coe d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.minimum
d_minimum_802 :: T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny
d_minimum_802 v0
  = coe
      d_minimum_534
      (coe d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.refl
d_refl_804 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny
d_refl_804 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_refl_804 v11
du_refl_804 :: T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny
du_refl_804 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_360 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_refl_104
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.reflexive
d_reflexive_806 ::
  T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_806 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_360
            (coe
               d_isLattice_530
               (coe
                  d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.supremum
d_supremum_808 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_808 v0
  = coe
      d_supremum_362
      (coe
         d_isLattice_530
         (coe d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.trans
d_trans_810 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_810 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            d_isPartialOrder_360
            (coe
               d_isLattice_530
               (coe
                  d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.transpose-⇨
d_transpose'45''8680'_812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8680'_812 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11
  = du_transpose'45''8680'_812 v11
du_transpose'45''8680'_812 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8680'_812 v0
  = coe
      du_transpose'45''8680'_638 (coe d_isHeytingAlgebra_772 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.transpose-∧
d_transpose'45''8743'_814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8743'_814 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11
  = du_transpose'45''8743'_814 v11
du_transpose'45''8743'_814 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8743'_814 v0
  = coe
      du_transpose'45''8743'_654 (coe d_isHeytingAlgebra_772 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.x∧y≤x
d_x'8743'y'8804'x_816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_816 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_x'8743'y'8804'x_816 v11
du_x'8743'y'8804'x_816 ::
  T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_816 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (coe
               du_x'8743'y'8804'x_200 (coe du_isMeetSemilattice_368 (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.x∧y≤y
d_x'8743'y'8804'y_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_818 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_x'8743'y'8804'y_818 v11
du_x'8743'y'8804'y_818 ::
  T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_818 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (coe
               du_x'8743'y'8804'y_212 (coe du_isMeetSemilattice_368 (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.x≤x∨y
d_x'8804'x'8744'y_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_820 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_x'8804'x'8744'y_820 v11
du_x'8804'x'8744'y_820 ::
  T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_820 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (coe
               du_x'8804'x'8744'y_38 (coe du_isJoinSemilattice_366 (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.y≤x∨y
d_y'8804'x'8744'y_822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_822 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_y'8804'x'8744'y_822 v11
du_y'8804'x'8744'y_822 ::
  T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_822 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (coe
               du_y'8804'x'8744'y_50 (coe du_isJoinSemilattice_366 (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.∧-greatest
d_'8743''45'greatest_824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_824 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 v11
  = du_'8743''45'greatest_824 v11
du_'8743''45'greatest_824 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_824 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (coe
               du_'8743''45'greatest_226
               (coe du_isMeetSemilattice_368 (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.∨-least
d_'8744''45'least_826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_826 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_'8744''45'least_826 v11
du_'8744''45'least_826 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_826 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (coe
               du_'8744''45'least_64 (coe du_isJoinSemilattice_366 (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.∼-resp-≈
d_'8764''45'resp'45''8776'_828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_746 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_828 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_'8764''45'resp'45''8776'_828 v11
du_'8764''45'resp'45''8776'_828 ::
  T_IsBooleanAlgebra_746 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_828 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_360 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_830 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8764''45'resp'691''45''8776'_830 v11
du_'8764''45'resp'691''45''8776'_830 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_830 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_360 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_832 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8764''45'resp'737''45''8776'_832 v11
du_'8764''45'resp'737''45''8776'_832 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_832 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_360 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.≲-resp-≈
d_'8818''45'resp'45''8776'_834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_746 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_834 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_'8818''45'resp'45''8776'_834 v11
du_'8818''45'resp'45''8776'_834 ::
  T_IsBooleanAlgebra_746 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_834 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_360 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_836 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8818''45'resp'691''45''8776'_836 v11
du_'8818''45'resp'691''45''8776'_836 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_836 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_360 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_838 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8818''45'resp'737''45''8776'_838 v11
du_'8818''45'resp'737''45''8776'_838 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_838 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_360 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.Eq.isPartialEquivalence
d_isPartialEquivalence_842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_746 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_842 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11
  = du_isPartialEquivalence_842 v11
du_isPartialEquivalence_842 ::
  T_IsBooleanAlgebra_746 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_842 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_360 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                        (coe v5)))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.Eq.refl
d_refl_844 :: T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny
d_refl_844 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_360
               (coe
                  d_isLattice_530
                  (coe
                     d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0)))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.Eq.reflexive
d_reflexive_846 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsBooleanAlgebra_746 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_846 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_reflexive_846 v11
du_reflexive_846 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_846 v0
  = let v1 = d_isHeytingAlgebra_772 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_628 (coe v1) in
       coe
         (let v3 = d_isLattice_530 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_360 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                          (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                       (coe
                          MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                          (coe v5))
                       v6)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.Eq.sym
d_sym_848 ::
  T_IsBooleanAlgebra_746 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_848 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_360
               (coe
                  d_isLattice_530
                  (coe
                     d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0)))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.Eq.trans
d_trans_850 ::
  T_IsBooleanAlgebra_746 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_850 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               d_isPartialOrder_360
               (coe
                  d_isLattice_530
                  (coe
                     d_isBoundedLattice_628 (coe d_isHeytingAlgebra_772 (coe v0)))))))
