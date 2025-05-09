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

module MAlonzo.Code.Relation.Binary.Lattice.Structures where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Lattice.Structures.IsJoinSemilattice
d_IsJoinSemilattice_22 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsJoinSemilattice_22
  = C_IsJoinSemilattice'46'constructor_527 MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
                                           (AgdaAny ->
                                            AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice.isPartialOrder
d_isPartialOrder_30 ::
  T_IsJoinSemilattice_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_30 v0
  = case coe v0 of
      C_IsJoinSemilattice'46'constructor_527 v1 v2 -> coe v1
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice.supremum
d_supremum_32 ::
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_32 v0
  = case coe v0 of
      C_IsJoinSemilattice'46'constructor_527 v1 v2 -> coe v2
      _                                            -> MAlonzo.RTE.mazUnreachableError
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
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe d_isPartialOrder_30 (coe v0))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.isEquivalence
d_isEquivalence_78 ::
  T_IsJoinSemilattice_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_78 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_30 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.isPreorder
d_isPreorder_80 ::
  T_IsJoinSemilattice_22 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_80 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
         MAlonzo.Code.Relation.Binary.Structures.du_refl_98
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.reflexive
d_reflexive_84 ::
  T_IsJoinSemilattice_22 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_84 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_30 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.trans
d_trans_86 ::
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_86 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
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
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
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
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
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
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
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
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
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
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
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
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.Eq.refl
d_refl_104 :: T_IsJoinSemilattice_22 -> AgdaAny -> AgdaAny
d_refl_104 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                 (coe v2))
              v3))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.Eq.sym
d_sym_108 ::
  T_IsJoinSemilattice_22 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_108 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_30 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsJoinSemilattice._.Eq.trans
d_trans_110 ::
  T_IsJoinSemilattice_22 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_110 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_30 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice
d_IsBoundedJoinSemilattice_116 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsBoundedJoinSemilattice_116
  = C_IsBoundedJoinSemilattice'46'constructor_5215 T_IsJoinSemilattice_22
                                                   (AgdaAny -> AgdaAny)
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice.isJoinSemilattice
d_isJoinSemilattice_126 ::
  T_IsBoundedJoinSemilattice_116 -> T_IsJoinSemilattice_22
d_isJoinSemilattice_126 v0
  = case coe v0 of
      C_IsBoundedJoinSemilattice'46'constructor_5215 v1 v2 -> coe v1
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice.minimum
d_minimum_128 ::
  T_IsBoundedJoinSemilattice_116 -> AgdaAny -> AgdaAny
d_minimum_128 v0
  = case coe v0 of
      C_IsBoundedJoinSemilattice'46'constructor_5215 v1 v2 -> coe v2
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.antisym
d_antisym_132 ::
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_132 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_126 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.isEquivalence
d_isEquivalence_134 ::
  T_IsBoundedJoinSemilattice_116 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_134 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_126 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.isPartialOrder
d_isPartialOrder_136 ::
  T_IsBoundedJoinSemilattice_116 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_136 v0
  = coe d_isPartialOrder_30 (coe d_isJoinSemilattice_126 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.isPreorder
d_isPreorder_138 ::
  T_IsBoundedJoinSemilattice_116 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_138 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_126 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.refl
d_refl_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsBoundedJoinSemilattice_116 -> AgdaAny -> AgdaAny
d_refl_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_140 v8
du_refl_140 :: T_IsBoundedJoinSemilattice_116 -> AgdaAny -> AgdaAny
du_refl_140 v0
  = let v1 = d_isJoinSemilattice_126 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_98
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.reflexive
d_reflexive_142 ::
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_142 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_126 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.supremum
d_supremum_144 ::
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_144 v0
  = coe d_supremum_32 (coe d_isJoinSemilattice_126 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.trans
d_trans_146 ::
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_146 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_126 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.x≤x∨y
d_x'8804'x'8744'y_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_116 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8804'x'8744'y_148 v8
du_x'8804'x'8744'y_148 ::
  T_IsBoundedJoinSemilattice_116 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_148 v0
  = coe du_x'8804'x'8744'y_38 (coe d_isJoinSemilattice_126 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.y≤x∨y
d_y'8804'x'8744'y_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_116 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_y'8804'x'8744'y_150 v8
du_y'8804'x'8744'y_150 ::
  T_IsBoundedJoinSemilattice_116 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_150 v0
  = coe du_y'8804'x'8744'y_50 (coe d_isJoinSemilattice_126 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.∨-least
d_'8744''45'least_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8744''45'least_152 v8
du_'8744''45'least_152 ::
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_152 v0
  = coe du_'8744''45'least_64 (coe d_isJoinSemilattice_126 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_116 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8764''45'resp'45''8776'_154 v8
du_'8764''45'resp'45''8776'_154 ::
  T_IsBoundedJoinSemilattice_116 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_154 v0
  = let v1 = d_isJoinSemilattice_126 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'691''45''8776'_156 v8
du_'8764''45'resp'691''45''8776'_156 ::
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_156 v0
  = let v1 = d_isJoinSemilattice_126 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'737''45''8776'_158 v8
du_'8764''45'resp'737''45''8776'_158 ::
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_158 v0
  = let v1 = d_isJoinSemilattice_126 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_116 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_160 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8818''45'resp'45''8776'_160 v8
du_'8818''45'resp'45''8776'_160 ::
  T_IsBoundedJoinSemilattice_116 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_160 v0
  = let v1 = d_isJoinSemilattice_126 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'691''45''8776'_162 v8
du_'8818''45'resp'691''45''8776'_162 ::
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_162 v0
  = let v1 = d_isJoinSemilattice_126 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'737''45''8776'_164 v8
du_'8818''45'resp'737''45''8776'_164 ::
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_164 v0
  = let v1 = d_isJoinSemilattice_126 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_116 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_168 v8
du_isPartialEquivalence_168 ::
  T_IsBoundedJoinSemilattice_116 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_168 v0
  = let v1 = d_isJoinSemilattice_126 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.Eq.refl
d_refl_170 :: T_IsBoundedJoinSemilattice_116 -> AgdaAny -> AgdaAny
d_refl_170 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_126 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.Eq.reflexive
d_reflexive_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_172 v8
du_reflexive_172 ::
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_172 v0
  = let v1 = d_isJoinSemilattice_126 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_30 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                    (coe v3))
                 v4)))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.Eq.sym
d_sym_174 ::
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_174 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_126 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedJoinSemilattice._.Eq.trans
d_trans_176 ::
  T_IsBoundedJoinSemilattice_116 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_176 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_30 (coe d_isJoinSemilattice_126 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice
d_IsMeetSemilattice_180 a0 a1 a2 a3 a4 a5 a6 = ()
data T_IsMeetSemilattice_180
  = C_IsMeetSemilattice'46'constructor_7577 MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
                                            (AgdaAny ->
                                             AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice.isPartialOrder
d_isPartialOrder_188 ::
  T_IsMeetSemilattice_180 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_188 v0
  = case coe v0 of
      C_IsMeetSemilattice'46'constructor_7577 v1 v2 -> coe v1
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice.infimum
d_infimum_190 ::
  T_IsMeetSemilattice_180 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_190 v0
  = case coe v0 of
      C_IsMeetSemilattice'46'constructor_7577 v1 v2 -> coe v2
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice.x∧y≤x
d_x'8743'y'8804'x_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_180 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_196 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_x'8743'y'8804'x_196 v7 v8 v9
du_x'8743'y'8804'x_196 ::
  T_IsMeetSemilattice_180 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_196 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_infimum_190 v0 v1 v2)
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice.x∧y≤y
d_x'8743'y'8804'y_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_180 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_x'8743'y'8804'y_208 v7 v8 v9
du_x'8743'y'8804'y_208 ::
  T_IsMeetSemilattice_180 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_208 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe d_infimum_190 v0 v1 v2))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice.∧-greatest
d_'8743''45'greatest_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_'8743''45'greatest_222 v7 v8 v9 v10
du_'8743''45'greatest_222 ::
  T_IsMeetSemilattice_180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_222 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe d_infimum_190 v0 v2 v3))
      v1
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.antisym
d_antisym_234 ::
  T_IsMeetSemilattice_180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_234 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe d_isPartialOrder_188 (coe v0))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.isEquivalence
d_isEquivalence_236 ::
  T_IsMeetSemilattice_180 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_236 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_188 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.isPreorder
d_isPreorder_238 ::
  T_IsMeetSemilattice_180 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_238 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe d_isPartialOrder_188 (coe v0))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.refl
d_refl_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_180 -> AgdaAny -> AgdaAny
d_refl_240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_refl_240 v7
du_refl_240 :: T_IsMeetSemilattice_180 -> AgdaAny -> AgdaAny
du_refl_240 v0
  = let v1 = d_isPartialOrder_188 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_98
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.reflexive
d_reflexive_242 ::
  T_IsMeetSemilattice_180 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_242 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_188 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.trans
d_trans_244 ::
  T_IsMeetSemilattice_180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_244 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_188 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_180 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8764''45'resp'45''8776'_246 v7
du_'8764''45'resp'45''8776'_246 ::
  T_IsMeetSemilattice_180 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_246 v0
  = let v1 = d_isPartialOrder_188 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8764''45'resp'691''45''8776'_248 v7
du_'8764''45'resp'691''45''8776'_248 ::
  T_IsMeetSemilattice_180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_248 v0
  = let v1 = d_isPartialOrder_188 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8764''45'resp'737''45''8776'_250 v7
du_'8764''45'resp'737''45''8776'_250 ::
  T_IsMeetSemilattice_180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_250 v0
  = let v1 = d_isPartialOrder_188 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_180 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8818''45'resp'45''8776'_252 v7
du_'8818''45'resp'45''8776'_252 ::
  T_IsMeetSemilattice_180 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_252 v0
  = let v1 = d_isPartialOrder_188 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8818''45'resp'691''45''8776'_254 v7
du_'8818''45'resp'691''45''8776'_254 ::
  T_IsMeetSemilattice_180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_254 v0
  = let v1 = d_isPartialOrder_188 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8818''45'resp'737''45''8776'_256 v7
du_'8818''45'resp'737''45''8776'_256 ::
  T_IsMeetSemilattice_180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_256 v0
  = let v1 = d_isPartialOrder_188 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_180 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isPartialEquivalence_260 v7
du_isPartialEquivalence_260 ::
  T_IsMeetSemilattice_180 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_260 v0
  = let v1 = d_isPartialOrder_188 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.Eq.refl
d_refl_262 :: T_IsMeetSemilattice_180 -> AgdaAny -> AgdaAny
d_refl_262 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_188 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.Eq.reflexive
d_reflexive_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsMeetSemilattice_180 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_reflexive_264 v7
du_reflexive_264 ::
  T_IsMeetSemilattice_180 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_264 v0
  = let v1 = d_isPartialOrder_188 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                 (coe v2))
              v3))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.Eq.sym
d_sym_266 ::
  T_IsMeetSemilattice_180 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_266 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_188 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsMeetSemilattice._.Eq.trans
d_trans_268 ::
  T_IsMeetSemilattice_180 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_268 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_188 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice
d_IsBoundedMeetSemilattice_274 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsBoundedMeetSemilattice_274
  = C_IsBoundedMeetSemilattice'46'constructor_12265 T_IsMeetSemilattice_180
                                                    (AgdaAny -> AgdaAny)
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice.isMeetSemilattice
d_isMeetSemilattice_284 ::
  T_IsBoundedMeetSemilattice_274 -> T_IsMeetSemilattice_180
d_isMeetSemilattice_284 v0
  = case coe v0 of
      C_IsBoundedMeetSemilattice'46'constructor_12265 v1 v2 -> coe v1
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice.maximum
d_maximum_286 ::
  T_IsBoundedMeetSemilattice_274 -> AgdaAny -> AgdaAny
d_maximum_286 v0
  = case coe v0 of
      C_IsBoundedMeetSemilattice'46'constructor_12265 v1 v2 -> coe v2
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.antisym
d_antisym_290 ::
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_290 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe d_isPartialOrder_188 (coe d_isMeetSemilattice_284 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.infimum
d_infimum_292 ::
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_292 v0
  = coe d_infimum_190 (coe d_isMeetSemilattice_284 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.isEquivalence
d_isEquivalence_294 ::
  T_IsBoundedMeetSemilattice_274 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_294 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_188 (coe d_isMeetSemilattice_284 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.isPartialOrder
d_isPartialOrder_296 ::
  T_IsBoundedMeetSemilattice_274 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_296 v0
  = coe d_isPartialOrder_188 (coe d_isMeetSemilattice_284 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.isPreorder
d_isPreorder_298 ::
  T_IsBoundedMeetSemilattice_274 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_298 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe d_isPartialOrder_188 (coe d_isMeetSemilattice_284 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.refl
d_refl_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsBoundedMeetSemilattice_274 -> AgdaAny -> AgdaAny
d_refl_300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_300 v8
du_refl_300 :: T_IsBoundedMeetSemilattice_274 -> AgdaAny -> AgdaAny
du_refl_300 v0
  = let v1 = d_isMeetSemilattice_284 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_188 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_98
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.reflexive
d_reflexive_302 ::
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_302 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_188 (coe d_isMeetSemilattice_284 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.trans
d_trans_304 ::
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_304 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_188 (coe d_isMeetSemilattice_284 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.x∧y≤x
d_x'8743'y'8804'x_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_274 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_306 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8743'y'8804'x_306 v8
du_x'8743'y'8804'x_306 ::
  T_IsBoundedMeetSemilattice_274 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_306 v0
  = coe du_x'8743'y'8804'x_196 (coe d_isMeetSemilattice_284 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.x∧y≤y
d_x'8743'y'8804'y_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_274 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8743'y'8804'y_308 v8
du_x'8743'y'8804'y_308 ::
  T_IsBoundedMeetSemilattice_274 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_308 v0
  = coe du_x'8743'y'8804'y_208 (coe d_isMeetSemilattice_284 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.∧-greatest
d_'8743''45'greatest_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8743''45'greatest_310 v8
du_'8743''45'greatest_310 ::
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_310 v0
  = coe
      du_'8743''45'greatest_222 (coe d_isMeetSemilattice_284 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_274 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8764''45'resp'45''8776'_312 v8
du_'8764''45'resp'45''8776'_312 ::
  T_IsBoundedMeetSemilattice_274 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_312 v0
  = let v1 = d_isMeetSemilattice_284 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_188 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'691''45''8776'_314 v8
du_'8764''45'resp'691''45''8776'_314 ::
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_314 v0
  = let v1 = d_isMeetSemilattice_284 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_188 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'737''45''8776'_316 v8
du_'8764''45'resp'737''45''8776'_316 ::
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_316 v0
  = let v1 = d_isMeetSemilattice_284 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_188 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_274 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_318 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8818''45'resp'45''8776'_318 v8
du_'8818''45'resp'45''8776'_318 ::
  T_IsBoundedMeetSemilattice_274 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_318 v0
  = let v1 = d_isMeetSemilattice_284 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_188 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_320 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'691''45''8776'_320 v8
du_'8818''45'resp'691''45''8776'_320 ::
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_320 v0
  = let v1 = d_isMeetSemilattice_284 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_188 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'737''45''8776'_322 v8
du_'8818''45'resp'737''45''8776'_322 ::
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_322 v0
  = let v1 = d_isMeetSemilattice_284 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_188 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_274 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_326 v8
du_isPartialEquivalence_326 ::
  T_IsBoundedMeetSemilattice_274 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_326 v0
  = let v1 = d_isMeetSemilattice_284 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_188 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.Eq.refl
d_refl_328 :: T_IsBoundedMeetSemilattice_274 -> AgdaAny -> AgdaAny
d_refl_328 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_188 (coe d_isMeetSemilattice_284 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.Eq.reflexive
d_reflexive_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_330 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_330 v8
du_reflexive_330 ::
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_330 v0
  = let v1 = d_isMeetSemilattice_284 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_188 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                    (coe v3))
                 v4)))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.Eq.sym
d_sym_332 ::
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_332 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_188 (coe d_isMeetSemilattice_284 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedMeetSemilattice._.Eq.trans
d_trans_334 ::
  T_IsBoundedMeetSemilattice_274 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_334 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_188 (coe d_isMeetSemilattice_284 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsLattice
d_IsLattice_340 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsLattice_340
  = C_IsLattice'46'constructor_14941 MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
                                     (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                                     (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Relation.Binary.Lattice.Structures.IsLattice.isPartialOrder
d_isPartialOrder_352 ::
  T_IsLattice_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_352 v0
  = case coe v0 of
      C_IsLattice'46'constructor_14941 v1 v2 v3 -> coe v1
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsLattice.supremum
d_supremum_354 ::
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_354 v0
  = case coe v0 of
      C_IsLattice'46'constructor_14941 v1 v2 v3 -> coe v2
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsLattice.infimum
d_infimum_356 ::
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_356 v0
  = case coe v0 of
      C_IsLattice'46'constructor_14941 v1 v2 v3 -> coe v3
      _                                         -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsLattice.isJoinSemilattice
d_isJoinSemilattice_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 -> T_IsJoinSemilattice_22
d_isJoinSemilattice_358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isJoinSemilattice_358 v8
du_isJoinSemilattice_358 ::
  T_IsLattice_340 -> T_IsJoinSemilattice_22
du_isJoinSemilattice_358 v0
  = coe
      C_IsJoinSemilattice'46'constructor_527
      (coe d_isPartialOrder_352 (coe v0)) (coe d_supremum_354 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice.isMeetSemilattice
d_isMeetSemilattice_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 -> T_IsMeetSemilattice_180
d_isMeetSemilattice_360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isMeetSemilattice_360 v8
du_isMeetSemilattice_360 ::
  T_IsLattice_340 -> T_IsMeetSemilattice_180
du_isMeetSemilattice_360 v0
  = coe
      C_IsMeetSemilattice'46'constructor_7577
      (coe d_isPartialOrder_352 (coe v0)) (coe d_infimum_356 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.x≤x∨y
d_x'8804'x'8744'y_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_364 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8804'x'8744'y_364 v8
du_x'8804'x'8744'y_364 ::
  T_IsLattice_340 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_364 v0
  = coe du_x'8804'x'8744'y_38 (coe du_isJoinSemilattice_358 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.y≤x∨y
d_y'8804'x'8744'y_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_y'8804'x'8744'y_366 v8
du_y'8804'x'8744'y_366 ::
  T_IsLattice_340 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_366 v0
  = coe du_y'8804'x'8744'y_50 (coe du_isJoinSemilattice_358 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.∨-least
d_'8744''45'least_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_368 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8744''45'least_368 v8
du_'8744''45'least_368 ::
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_368 v0
  = coe du_'8744''45'least_64 (coe du_isJoinSemilattice_358 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.x∧y≤x
d_x'8743'y'8804'x_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_372 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8743'y'8804'x_372 v8
du_x'8743'y'8804'x_372 ::
  T_IsLattice_340 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_372 v0
  = coe
      du_x'8743'y'8804'x_196 (coe du_isMeetSemilattice_360 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.x∧y≤y
d_x'8743'y'8804'y_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_374 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8743'y'8804'y_374 v8
du_x'8743'y'8804'y_374 ::
  T_IsLattice_340 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_374 v0
  = coe
      du_x'8743'y'8804'y_208 (coe du_isMeetSemilattice_360 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.∧-greatest
d_'8743''45'greatest_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_376 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8743''45'greatest_376 v8
du_'8743''45'greatest_376 ::
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_376 v0
  = coe
      du_'8743''45'greatest_222 (coe du_isMeetSemilattice_360 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.antisym
d_antisym_380 ::
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_380 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe d_isPartialOrder_352 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.isEquivalence
d_isEquivalence_382 ::
  T_IsLattice_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_382 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_352 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsLattice._.isPreorder
d_isPreorder_384 ::
  T_IsLattice_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_384 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe d_isPartialOrder_352 (coe v0))
-- Relation.Binary.Lattice.Structures.IsLattice._.refl
d_refl_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 -> AgdaAny -> AgdaAny
d_refl_386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_386 v8
du_refl_386 :: T_IsLattice_340 -> AgdaAny -> AgdaAny
du_refl_386 v0
  = let v1 = d_isPartialOrder_352 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_98
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsLattice._.reflexive
d_reflexive_388 ::
  T_IsLattice_340 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_388 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_352 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsLattice._.trans
d_trans_390 ::
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_390 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_352 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsLattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8764''45'resp'45''8776'_392 v8
du_'8764''45'resp'45''8776'_392 ::
  T_IsLattice_340 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_392 v0
  = let v1 = d_isPartialOrder_352 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsLattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'691''45''8776'_394 v8
du_'8764''45'resp'691''45''8776'_394 ::
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_394 v0
  = let v1 = d_isPartialOrder_352 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsLattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'737''45''8776'_396 v8
du_'8764''45'resp'737''45''8776'_396 ::
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_396 v0
  = let v1 = d_isPartialOrder_352 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsLattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_398 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8818''45'resp'45''8776'_398 v8
du_'8818''45'resp'45''8776'_398 ::
  T_IsLattice_340 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_398 v0
  = let v1 = d_isPartialOrder_352 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsLattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_400 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'691''45''8776'_400 v8
du_'8818''45'resp'691''45''8776'_400 ::
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_400 v0
  = let v1 = d_isPartialOrder_352 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsLattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_402 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'737''45''8776'_402 v8
du_'8818''45'resp'737''45''8776'_402 ::
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_402 v0
  = let v1 = d_isPartialOrder_352 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsLattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_406 v8
du_isPartialEquivalence_406 ::
  T_IsLattice_340 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_406 v0
  = let v1 = d_isPartialOrder_352 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsLattice._.Eq.refl
d_refl_408 :: T_IsLattice_340 -> AgdaAny -> AgdaAny
d_refl_408 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_352 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsLattice._.Eq.reflexive
d_reflexive_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsLattice_340 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_410 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_410 v8
du_reflexive_410 ::
  T_IsLattice_340 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_410 v0
  = let v1 = d_isPartialOrder_352 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                 (coe v2))
              v3))
-- Relation.Binary.Lattice.Structures.IsLattice._.Eq.sym
d_sym_412 ::
  T_IsLattice_340 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_412 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_352 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsLattice._.Eq.trans
d_trans_414 ::
  T_IsLattice_340 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_414 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_352 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice
d_IsDistributiveLattice_420 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_IsDistributiveLattice_420
  = C_IsDistributiveLattice'46'constructor_18193 T_IsLattice_340
                                                 (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice.isLattice
d_isLattice_430 :: T_IsDistributiveLattice_420 -> T_IsLattice_340
d_isLattice_430 v0
  = case coe v0 of
      C_IsDistributiveLattice'46'constructor_18193 v1 v2 -> coe v1
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_432 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8744'_432 v0
  = case coe v0 of
      C_IsDistributiveLattice'46'constructor_18193 v1 v2 -> coe v2
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.antisym
d_antisym_436 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_436 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe d_isPartialOrder_352 (coe d_isLattice_430 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.infimum
d_infimum_438 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_438 v0 = coe d_infimum_356 (coe d_isLattice_430 (coe v0))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.isEquivalence
d_isEquivalence_440 ::
  T_IsDistributiveLattice_420 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_440 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_352 (coe d_isLattice_430 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.isJoinSemilattice
d_isJoinSemilattice_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 -> T_IsJoinSemilattice_22
d_isJoinSemilattice_442 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isJoinSemilattice_442 v8
du_isJoinSemilattice_442 ::
  T_IsDistributiveLattice_420 -> T_IsJoinSemilattice_22
du_isJoinSemilattice_442 v0
  = coe du_isJoinSemilattice_358 (coe d_isLattice_430 (coe v0))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.isMeetSemilattice
d_isMeetSemilattice_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 -> T_IsMeetSemilattice_180
d_isMeetSemilattice_444 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isMeetSemilattice_444 v8
du_isMeetSemilattice_444 ::
  T_IsDistributiveLattice_420 -> T_IsMeetSemilattice_180
du_isMeetSemilattice_444 v0
  = coe du_isMeetSemilattice_360 (coe d_isLattice_430 (coe v0))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.isPartialOrder
d_isPartialOrder_446 ::
  T_IsDistributiveLattice_420 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_446 v0
  = coe d_isPartialOrder_352 (coe d_isLattice_430 (coe v0))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.isPreorder
d_isPreorder_448 ::
  T_IsDistributiveLattice_420 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_448 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe d_isPartialOrder_352 (coe d_isLattice_430 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.refl
d_refl_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 -> AgdaAny -> AgdaAny
d_refl_450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_refl_450 v8
du_refl_450 :: T_IsDistributiveLattice_420 -> AgdaAny -> AgdaAny
du_refl_450 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_98
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.reflexive
d_reflexive_452 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_452 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_352 (coe d_isLattice_430 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.supremum
d_supremum_454 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_454 v0
  = coe d_supremum_354 (coe d_isLattice_430 (coe v0))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.trans
d_trans_456 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_456 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_352 (coe d_isLattice_430 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.x∧y≤x
d_x'8743'y'8804'x_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_458 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8743'y'8804'x_458 v8
du_x'8743'y'8804'x_458 ::
  T_IsDistributiveLattice_420 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_458 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (coe
         du_x'8743'y'8804'x_196 (coe du_isMeetSemilattice_360 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.x∧y≤y
d_x'8743'y'8804'y_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_460 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8743'y'8804'y_460 v8
du_x'8743'y'8804'y_460 ::
  T_IsDistributiveLattice_420 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_460 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (coe
         du_x'8743'y'8804'y_208 (coe du_isMeetSemilattice_360 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.x≤x∨y
d_x'8804'x'8744'y_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_462 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_x'8804'x'8744'y_462 v8
du_x'8804'x'8744'y_462 ::
  T_IsDistributiveLattice_420 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_462 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (coe du_x'8804'x'8744'y_38 (coe du_isJoinSemilattice_358 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.y≤x∨y
d_y'8804'x'8744'y_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_464 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_y'8804'x'8744'y_464 v8
du_y'8804'x'8744'y_464 ::
  T_IsDistributiveLattice_420 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_464 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (coe du_y'8804'x'8744'y_50 (coe du_isJoinSemilattice_358 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.∧-greatest
d_'8743''45'greatest_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_466 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8743''45'greatest_466 v8
du_'8743''45'greatest_466 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_466 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (coe
         du_'8743''45'greatest_222 (coe du_isMeetSemilattice_360 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.∨-least
d_'8744''45'least_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_468 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8744''45'least_468 v8
du_'8744''45'least_468 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_468 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (coe du_'8744''45'least_64 (coe du_isJoinSemilattice_358 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_470 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8764''45'resp'45''8776'_470 v8
du_'8764''45'resp'45''8776'_470 ::
  T_IsDistributiveLattice_420 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_470 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_472 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'691''45''8776'_472 v8
du_'8764''45'resp'691''45''8776'_472 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_472 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_474 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8764''45'resp'737''45''8776'_474 v8
du_'8764''45'resp'737''45''8776'_474 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_474 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_476 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_'8818''45'resp'45''8776'_476 v8
du_'8818''45'resp'45''8776'_476 ::
  T_IsDistributiveLattice_420 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_476 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_478 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'691''45''8776'_478 v8
du_'8818''45'resp'691''45''8776'_478 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_478 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_480 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    v8
  = du_'8818''45'resp'737''45''8776'_480 v8
du_'8818''45'resp'737''45''8776'_480 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_480 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_isPartialEquivalence_484 v8
du_isPartialEquivalence_484 ::
  T_IsDistributiveLattice_420 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_484 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.Eq.refl
d_refl_486 :: T_IsDistributiveLattice_420 -> AgdaAny -> AgdaAny
d_refl_486 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_352 (coe d_isLattice_430 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.Eq.reflexive
d_reflexive_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_IsDistributiveLattice_420 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_488 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_reflexive_488 v8
du_reflexive_488 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_488 v0
  = let v1 = d_isLattice_430 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                    (coe v3))
                 v4)))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.Eq.sym
d_sym_490 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_490 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_352 (coe d_isLattice_430 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsDistributiveLattice._.Eq.trans
d_trans_492 ::
  T_IsDistributiveLattice_420 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_492 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_352 (coe d_isLattice_430 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice
d_IsBoundedLattice_502 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
data T_IsBoundedLattice_502
  = C_IsBoundedLattice'46'constructor_21319 T_IsLattice_340
                                            (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
-- Relation.Binary.Lattice.Structures.IsBoundedLattice.isLattice
d_isLattice_518 :: T_IsBoundedLattice_502 -> T_IsLattice_340
d_isLattice_518 v0
  = case coe v0 of
      C_IsBoundedLattice'46'constructor_21319 v1 v2 v3 -> coe v1
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBoundedLattice.maximum
d_maximum_520 :: T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny
d_maximum_520 v0
  = case coe v0 of
      C_IsBoundedLattice'46'constructor_21319 v1 v2 v3 -> coe v2
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBoundedLattice.minimum
d_minimum_522 :: T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny
d_minimum_522 v0
  = case coe v0 of
      C_IsBoundedLattice'46'constructor_21319 v1 v2 v3 -> coe v3
      _                                                -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.antisym
d_antisym_526 ::
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_526 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe d_isPartialOrder_352 (coe d_isLattice_518 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.infimum
d_infimum_528 ::
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_528 v0 = coe d_infimum_356 (coe d_isLattice_518 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.isEquivalence
d_isEquivalence_530 ::
  T_IsBoundedLattice_502 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_530 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_352 (coe d_isLattice_518 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.isJoinSemilattice
d_isJoinSemilattice_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_502 -> T_IsJoinSemilattice_22
d_isJoinSemilattice_532 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isJoinSemilattice_532 v10
du_isJoinSemilattice_532 ::
  T_IsBoundedLattice_502 -> T_IsJoinSemilattice_22
du_isJoinSemilattice_532 v0
  = coe du_isJoinSemilattice_358 (coe d_isLattice_518 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.isMeetSemilattice
d_isMeetSemilattice_534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_502 -> T_IsMeetSemilattice_180
d_isMeetSemilattice_534 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isMeetSemilattice_534 v10
du_isMeetSemilattice_534 ::
  T_IsBoundedLattice_502 -> T_IsMeetSemilattice_180
du_isMeetSemilattice_534 v0
  = coe du_isMeetSemilattice_360 (coe d_isLattice_518 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.isPartialOrder
d_isPartialOrder_536 ::
  T_IsBoundedLattice_502 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_536 v0
  = coe d_isPartialOrder_352 (coe d_isLattice_518 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.isPreorder
d_isPreorder_538 ::
  T_IsBoundedLattice_502 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_538 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe d_isPartialOrder_352 (coe d_isLattice_518 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.refl
d_refl_540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny
d_refl_540 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_refl_540 v10
du_refl_540 :: T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny
du_refl_540 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_98
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.reflexive
d_reflexive_542 ::
  T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_542 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_352 (coe d_isLattice_518 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.supremum
d_supremum_544 ::
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_544 v0
  = coe d_supremum_354 (coe d_isLattice_518 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.trans
d_trans_546 ::
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_546 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe d_isPartialOrder_352 (coe d_isLattice_518 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.x∧y≤x
d_x'8743'y'8804'x_548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_548 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_x'8743'y'8804'x_548 v10
du_x'8743'y'8804'x_548 ::
  T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_548 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (coe
         du_x'8743'y'8804'x_196 (coe du_isMeetSemilattice_360 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.x∧y≤y
d_x'8743'y'8804'y_550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_550 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_x'8743'y'8804'y_550 v10
du_x'8743'y'8804'y_550 ::
  T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_550 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (coe
         du_x'8743'y'8804'y_208 (coe du_isMeetSemilattice_360 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.x≤x∨y
d_x'8804'x'8744'y_552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_552 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_x'8804'x'8744'y_552 v10
du_x'8804'x'8744'y_552 ::
  T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_552 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (coe du_x'8804'x'8744'y_38 (coe du_isJoinSemilattice_358 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.y≤x∨y
d_y'8804'x'8744'y_554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_554 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_y'8804'x'8744'y_554 v10
du_y'8804'x'8744'y_554 ::
  T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_554 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (coe du_y'8804'x'8744'y_50 (coe du_isJoinSemilattice_358 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.∧-greatest
d_'8743''45'greatest_556 ::
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
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_556 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         v10
  = du_'8743''45'greatest_556 v10
du_'8743''45'greatest_556 ::
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_556 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (coe
         du_'8743''45'greatest_222 (coe du_isMeetSemilattice_360 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.∨-least
d_'8744''45'least_558 ::
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
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_558 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_'8744''45'least_558 v10
du_'8744''45'least_558 ::
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_558 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (coe du_'8744''45'least_64 (coe du_isJoinSemilattice_358 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_560 ::
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
  T_IsBoundedLattice_502 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_560 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 v10
  = du_'8764''45'resp'45''8776'_560 v10
du_'8764''45'resp'45''8776'_560 ::
  T_IsBoundedLattice_502 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_560 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_562 ::
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
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_562 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 v10
  = du_'8764''45'resp'691''45''8776'_562 v10
du_'8764''45'resp'691''45''8776'_562 ::
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_562 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_564 ::
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
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_564 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 v10
  = du_'8764''45'resp'737''45''8776'_564 v10
du_'8764''45'resp'737''45''8776'_564 ::
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_564 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_566 ::
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
  T_IsBoundedLattice_502 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_566 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 v10
  = du_'8818''45'resp'45''8776'_566 v10
du_'8818''45'resp'45''8776'_566 ::
  T_IsBoundedLattice_502 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_566 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_568 ::
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
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_568 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 v10
  = du_'8818''45'resp'691''45''8776'_568 v10
du_'8818''45'resp'691''45''8776'_568 ::
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_568 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_570 ::
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
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_570 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 v10
  = du_'8818''45'resp'737''45''8776'_570 v10
du_'8818''45'resp'737''45''8776'_570 ::
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_570 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_574 ::
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
  T_IsBoundedLattice_502 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           v10
  = du_isPartialEquivalence_574 v10
du_isPartialEquivalence_574 ::
  T_IsBoundedLattice_502 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_574 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.Eq.refl
d_refl_576 :: T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny
d_refl_576 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_352 (coe d_isLattice_518 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.Eq.reflexive
d_reflexive_578 ::
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
  T_IsBoundedLattice_502 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_578 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_reflexive_578 v10
du_reflexive_578 ::
  T_IsBoundedLattice_502 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_578 v0
  = let v1 = d_isLattice_518 (coe v0) in
    coe
      (let v2 = d_isPartialOrder_352 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                    (coe v3))
                 v4)))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.Eq.sym
d_sym_580 ::
  T_IsBoundedLattice_502 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_580 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_352 (coe d_isLattice_518 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice._.Eq.trans
d_trans_582 ::
  T_IsBoundedLattice_502 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_582 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe d_isPartialOrder_352 (coe d_isLattice_518 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_502 -> T_IsBoundedJoinSemilattice_116
d_isBoundedJoinSemilattice_584 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 v10
  = du_isBoundedJoinSemilattice_584 v10
du_isBoundedJoinSemilattice_584 ::
  T_IsBoundedLattice_502 -> T_IsBoundedJoinSemilattice_116
du_isBoundedJoinSemilattice_584 v0
  = coe
      C_IsBoundedJoinSemilattice'46'constructor_5215
      (coe du_isJoinSemilattice_358 (coe d_isLattice_518 (coe v0)))
      (coe d_minimum_522 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBoundedLattice.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsBoundedLattice_502 -> T_IsBoundedMeetSemilattice_274
d_isBoundedMeetSemilattice_586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 v10
  = du_isBoundedMeetSemilattice_586 v10
du_isBoundedMeetSemilattice_586 ::
  T_IsBoundedLattice_502 -> T_IsBoundedMeetSemilattice_274
du_isBoundedMeetSemilattice_586 v0
  = coe
      C_IsBoundedMeetSemilattice'46'constructor_12265
      (coe du_isMeetSemilattice_360 (coe d_isLattice_518 (coe v0)))
      (coe d_maximum_520 (coe v0))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra
d_IsHeytingAlgebra_598 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_IsHeytingAlgebra_598
  = C_IsHeytingAlgebra'46'constructor_25303 T_IsBoundedLattice_502
                                            (AgdaAny ->
                                             AgdaAny ->
                                             AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra.isBoundedLattice
d_isBoundedLattice_614 ::
  T_IsHeytingAlgebra_598 -> T_IsBoundedLattice_502
d_isBoundedLattice_614 v0
  = case coe v0 of
      C_IsHeytingAlgebra'46'constructor_25303 v1 v2 -> coe v1
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra.exponential
d_exponential_616 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exponential_616 v0
  = case coe v0 of
      C_IsHeytingAlgebra'46'constructor_25303 v1 v2 -> coe v2
      _                                             -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra.transpose-⇨
d_transpose'45''8680'_624 ::
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
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8680'_624 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11 v12 v13 v14
  = du_transpose'45''8680'_624 v11 v12 v13 v14
du_transpose'45''8680'_624 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8680'_624 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_exponential_616 v0 v1 v2 v3)
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra.transpose-∧
d_transpose'45''8743'_640 ::
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
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8743'_640 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11 v12 v13 v14
  = du_transpose'45''8743'_640 v11 v12 v13 v14
du_transpose'45''8743'_640 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8743'_640 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_exponential_616 v0 v1 v2 v3)
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.antisym
d_antisym_652 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_652 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         d_isPartialOrder_352
         (coe d_isLattice_518 (coe d_isBoundedLattice_614 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.infimum
d_infimum_654 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_654 v0
  = coe
      d_infimum_356
      (coe d_isLattice_518 (coe d_isBoundedLattice_614 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_656 ::
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
  AgdaAny -> T_IsHeytingAlgebra_598 -> T_IsBoundedJoinSemilattice_116
d_isBoundedJoinSemilattice_656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_isBoundedJoinSemilattice_656 v11
du_isBoundedJoinSemilattice_656 ::
  T_IsHeytingAlgebra_598 -> T_IsBoundedJoinSemilattice_116
du_isBoundedJoinSemilattice_656 v0
  = coe
      du_isBoundedJoinSemilattice_584
      (coe d_isBoundedLattice_614 (coe v0))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_658 ::
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
  AgdaAny -> T_IsHeytingAlgebra_598 -> T_IsBoundedMeetSemilattice_274
d_isBoundedMeetSemilattice_658 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_isBoundedMeetSemilattice_658 v11
du_isBoundedMeetSemilattice_658 ::
  T_IsHeytingAlgebra_598 -> T_IsBoundedMeetSemilattice_274
du_isBoundedMeetSemilattice_658 v0
  = coe
      du_isBoundedMeetSemilattice_586
      (coe d_isBoundedLattice_614 (coe v0))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isEquivalence
d_isEquivalence_660 ::
  T_IsHeytingAlgebra_598 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_660 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_352
            (coe d_isLattice_518 (coe d_isBoundedLattice_614 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isJoinSemilattice
d_isJoinSemilattice_662 ::
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
  AgdaAny -> T_IsHeytingAlgebra_598 -> T_IsJoinSemilattice_22
d_isJoinSemilattice_662 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 v11
  = du_isJoinSemilattice_662 v11
du_isJoinSemilattice_662 ::
  T_IsHeytingAlgebra_598 -> T_IsJoinSemilattice_22
du_isJoinSemilattice_662 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe (coe du_isJoinSemilattice_358 (coe d_isLattice_518 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isLattice
d_isLattice_664 :: T_IsHeytingAlgebra_598 -> T_IsLattice_340
d_isLattice_664 v0
  = coe d_isLattice_518 (coe d_isBoundedLattice_614 (coe v0))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isMeetSemilattice
d_isMeetSemilattice_666 ::
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
  AgdaAny -> T_IsHeytingAlgebra_598 -> T_IsMeetSemilattice_180
d_isMeetSemilattice_666 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 v11
  = du_isMeetSemilattice_666 v11
du_isMeetSemilattice_666 ::
  T_IsHeytingAlgebra_598 -> T_IsMeetSemilattice_180
du_isMeetSemilattice_666 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe (coe du_isMeetSemilattice_360 (coe d_isLattice_518 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isPartialOrder
d_isPartialOrder_668 ::
  T_IsHeytingAlgebra_598 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_668 v0
  = coe
      d_isPartialOrder_352
      (coe d_isLattice_518 (coe d_isBoundedLattice_614 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.isPreorder
d_isPreorder_670 ::
  T_IsHeytingAlgebra_598 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_670 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         d_isPartialOrder_352
         (coe d_isLattice_518 (coe d_isBoundedLattice_614 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.maximum
d_maximum_672 :: T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny
d_maximum_672 v0
  = coe d_maximum_520 (coe d_isBoundedLattice_614 (coe v0))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.minimum
d_minimum_674 :: T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny
d_minimum_674 v0
  = coe d_minimum_522 (coe d_isBoundedLattice_614 (coe v0))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.refl
d_refl_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny
d_refl_676 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_refl_676 v11
du_refl_676 :: T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny
du_refl_676 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_352 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_98
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.reflexive
d_reflexive_678 ::
  T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_678 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_352
            (coe d_isLattice_518 (coe d_isBoundedLattice_614 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.supremum
d_supremum_680 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_680 v0
  = coe
      d_supremum_354
      (coe d_isLattice_518 (coe d_isBoundedLattice_614 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.trans
d_trans_682 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_682 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_352
            (coe d_isLattice_518 (coe d_isBoundedLattice_614 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.x∧y≤x
d_x'8743'y'8804'x_684 ::
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
  AgdaAny -> T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_684 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_x'8743'y'8804'x_684 v11
du_x'8743'y'8804'x_684 ::
  T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_684 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (coe
            du_x'8743'y'8804'x_196 (coe du_isMeetSemilattice_360 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.x∧y≤y
d_x'8743'y'8804'y_686 ::
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
  AgdaAny -> T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_686 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_x'8743'y'8804'y_686 v11
du_x'8743'y'8804'y_686 ::
  T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_686 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (coe
            du_x'8743'y'8804'y_208 (coe du_isMeetSemilattice_360 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.x≤x∨y
d_x'8804'x'8744'y_688 ::
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
  AgdaAny -> T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_688 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_x'8804'x'8744'y_688 v11
du_x'8804'x'8744'y_688 ::
  T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_688 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (coe
            du_x'8804'x'8744'y_38 (coe du_isJoinSemilattice_358 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.y≤x∨y
d_y'8804'x'8744'y_690 ::
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
  AgdaAny -> T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_690 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_y'8804'x'8744'y_690 v11
du_y'8804'x'8744'y_690 ::
  T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_690 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (coe
            du_y'8804'x'8744'y_50 (coe du_isJoinSemilattice_358 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.∧-greatest
d_'8743''45'greatest_692 ::
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
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_692 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 v11
  = du_'8743''45'greatest_692 v11
du_'8743''45'greatest_692 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_692 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (coe
            du_'8743''45'greatest_222 (coe du_isMeetSemilattice_360 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.∨-least
d_'8744''45'least_694 ::
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
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_694 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_'8744''45'least_694 v11
du_'8744''45'least_694 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_694 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (coe
            du_'8744''45'least_64 (coe du_isJoinSemilattice_358 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.∼-resp-≈
d_'8764''45'resp'45''8776'_696 ::
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
  T_IsHeytingAlgebra_598 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_696 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_'8764''45'resp'45''8776'_696 v11
du_'8764''45'resp'45''8776'_696 ::
  T_IsHeytingAlgebra_598 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_696 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_352 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_698 ::
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
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8764''45'resp'691''45''8776'_698 v11
du_'8764''45'resp'691''45''8776'_698 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_698 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_352 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_700 ::
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
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_700 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8764''45'resp'737''45''8776'_700 v11
du_'8764''45'resp'737''45''8776'_700 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_700 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_352 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.≲-resp-≈
d_'8818''45'resp'45''8776'_702 ::
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
  T_IsHeytingAlgebra_598 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_702 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_'8818''45'resp'45''8776'_702 v11
du_'8818''45'resp'45''8776'_702 ::
  T_IsHeytingAlgebra_598 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_702 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_352 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_704 ::
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
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_704 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8818''45'resp'691''45''8776'_704 v11
du_'8818''45'resp'691''45''8776'_704 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_704 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_352 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_706 ::
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
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8818''45'resp'737''45''8776'_706 v11
du_'8818''45'resp'737''45''8776'_706 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_706 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_352 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.Eq.isPartialEquivalence
d_isPartialEquivalence_710 ::
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
  T_IsHeytingAlgebra_598 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_710 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11
  = du_isPartialEquivalence_710 v11
du_isPartialEquivalence_710 ::
  T_IsHeytingAlgebra_598 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_710 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_352 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.Eq.refl
d_refl_712 :: T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny
d_refl_712 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_352
               (coe d_isLattice_518 (coe d_isBoundedLattice_614 (coe v0))))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.Eq.reflexive
d_reflexive_714 ::
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
  T_IsHeytingAlgebra_598 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_714 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_reflexive_714 v11
du_reflexive_714 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_714 v0
  = let v1 = d_isBoundedLattice_614 (coe v0) in
    coe
      (let v2 = d_isLattice_518 (coe v1) in
       coe
         (let v3 = d_isPartialOrder_352 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                       (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                       (coe v4))
                    v5))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.Eq.sym
d_sym_716 ::
  T_IsHeytingAlgebra_598 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_716 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_352
               (coe d_isLattice_518 (coe d_isBoundedLattice_614 (coe v0))))))
-- Relation.Binary.Lattice.Structures.IsHeytingAlgebra._.Eq.trans
d_trans_718 ::
  T_IsHeytingAlgebra_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_718 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_352
               (coe d_isLattice_518 (coe d_isBoundedLattice_614 (coe v0))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra
d_IsBooleanAlgebra_730 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
newtype T_IsBooleanAlgebra_730
  = C_IsBooleanAlgebra'46'constructor_31651 T_IsHeytingAlgebra_598
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._⇨_
d__'8680'__750 ::
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
  AgdaAny -> T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8680'__750 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10 ~v11 v12
               v13
  = du__'8680'__750 v6 v8 v12 v13
du__'8680'__750 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'8680'__750 v0 v1 v2 v3 = coe v0 (coe v1 v2) v3
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra.isHeytingAlgebra
d_isHeytingAlgebra_756 ::
  T_IsBooleanAlgebra_730 -> T_IsHeytingAlgebra_598
d_isHeytingAlgebra_756 v0
  = case coe v0 of
      C_IsBooleanAlgebra'46'constructor_31651 v1 -> coe v1
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.antisym
d_antisym_760 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_760 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         d_isPartialOrder_352
         (coe
            d_isLattice_518
            (coe
               d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.exponential
d_exponential_762 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exponential_762 v0
  = coe d_exponential_616 (coe d_isHeytingAlgebra_756 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.infimum
d_infimum_764 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_764 v0
  = coe
      d_infimum_356
      (coe
         d_isLattice_518
         (coe d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_766 ::
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
  AgdaAny -> T_IsBooleanAlgebra_730 -> T_IsBoundedJoinSemilattice_116
d_isBoundedJoinSemilattice_766 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_isBoundedJoinSemilattice_766 v11
du_isBoundedJoinSemilattice_766 ::
  T_IsBooleanAlgebra_730 -> T_IsBoundedJoinSemilattice_116
du_isBoundedJoinSemilattice_766 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (coe
         du_isBoundedJoinSemilattice_584
         (coe d_isBoundedLattice_614 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isBoundedLattice
d_isBoundedLattice_768 ::
  T_IsBooleanAlgebra_730 -> T_IsBoundedLattice_502
d_isBoundedLattice_768 v0
  = coe d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_770 ::
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
  AgdaAny -> T_IsBooleanAlgebra_730 -> T_IsBoundedMeetSemilattice_274
d_isBoundedMeetSemilattice_770 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_isBoundedMeetSemilattice_770 v11
du_isBoundedMeetSemilattice_770 ::
  T_IsBooleanAlgebra_730 -> T_IsBoundedMeetSemilattice_274
du_isBoundedMeetSemilattice_770 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (coe
         du_isBoundedMeetSemilattice_586
         (coe d_isBoundedLattice_614 (coe v1)))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isEquivalence
d_isEquivalence_772 ::
  T_IsBooleanAlgebra_730 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_772 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_352
            (coe
               d_isLattice_518
               (coe
                  d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isJoinSemilattice
d_isJoinSemilattice_774 ::
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
  AgdaAny -> T_IsBooleanAlgebra_730 -> T_IsJoinSemilattice_22
d_isJoinSemilattice_774 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 v11
  = du_isJoinSemilattice_774 v11
du_isJoinSemilattice_774 ::
  T_IsBooleanAlgebra_730 -> T_IsJoinSemilattice_22
du_isJoinSemilattice_774 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe (coe du_isJoinSemilattice_358 (coe d_isLattice_518 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isLattice
d_isLattice_776 :: T_IsBooleanAlgebra_730 -> T_IsLattice_340
d_isLattice_776 v0
  = coe
      d_isLattice_518
      (coe d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isMeetSemilattice
d_isMeetSemilattice_778 ::
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
  AgdaAny -> T_IsBooleanAlgebra_730 -> T_IsMeetSemilattice_180
d_isMeetSemilattice_778 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 v11
  = du_isMeetSemilattice_778 v11
du_isMeetSemilattice_778 ::
  T_IsBooleanAlgebra_730 -> T_IsMeetSemilattice_180
du_isMeetSemilattice_778 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe (coe du_isMeetSemilattice_360 (coe d_isLattice_518 (coe v2))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isPartialOrder
d_isPartialOrder_780 ::
  T_IsBooleanAlgebra_730 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_780 v0
  = coe
      d_isPartialOrder_352
      (coe
         d_isLattice_518
         (coe d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.isPreorder
d_isPreorder_782 ::
  T_IsBooleanAlgebra_730 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_782 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         d_isPartialOrder_352
         (coe
            d_isLattice_518
            (coe
               d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.maximum
d_maximum_784 :: T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny
d_maximum_784 v0
  = coe
      d_maximum_520
      (coe d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.minimum
d_minimum_786 :: T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny
d_minimum_786 v0
  = coe
      d_minimum_522
      (coe d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0)))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.refl
d_refl_788 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny
d_refl_788 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_refl_788 v11
du_refl_788 :: T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny
du_refl_788 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_352 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.reflexive
d_reflexive_790 ::
  T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_790 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_352
            (coe
               d_isLattice_518
               (coe
                  d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.supremum
d_supremum_792 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_792 v0
  = coe
      d_supremum_354
      (coe
         d_isLattice_518
         (coe d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.trans
d_trans_794 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_794 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            d_isPartialOrder_352
            (coe
               d_isLattice_518
               (coe
                  d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.transpose-⇨
d_transpose'45''8680'_796 ::
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
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8680'_796 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11
  = du_transpose'45''8680'_796 v11
du_transpose'45''8680'_796 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8680'_796 v0
  = coe
      du_transpose'45''8680'_624 (coe d_isHeytingAlgebra_756 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.transpose-∧
d_transpose'45''8743'_798 ::
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
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8743'_798 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11
  = du_transpose'45''8743'_798 v11
du_transpose'45''8743'_798 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8743'_798 v0
  = coe
      du_transpose'45''8743'_640 (coe d_isHeytingAlgebra_756 (coe v0))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.x∧y≤x
d_x'8743'y'8804'x_800 ::
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
  AgdaAny -> T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_800 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_x'8743'y'8804'x_800 v11
du_x'8743'y'8804'x_800 ::
  T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_800 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (coe
               du_x'8743'y'8804'x_196 (coe du_isMeetSemilattice_360 (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.x∧y≤y
d_x'8743'y'8804'y_802 ::
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
  AgdaAny -> T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_802 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_x'8743'y'8804'y_802 v11
du_x'8743'y'8804'y_802 ::
  T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_802 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (coe
               du_x'8743'y'8804'y_208 (coe du_isMeetSemilattice_360 (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.x≤x∨y
d_x'8804'x'8744'y_804 ::
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
  AgdaAny -> T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_804 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_x'8804'x'8744'y_804 v11
du_x'8804'x'8744'y_804 ::
  T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_804 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (coe
               du_x'8804'x'8744'y_38 (coe du_isJoinSemilattice_358 (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.y≤x∨y
d_y'8804'x'8744'y_806 ::
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
  AgdaAny -> T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_806 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_y'8804'x'8744'y_806 v11
du_y'8804'x'8744'y_806 ::
  T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_806 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (coe
               du_y'8804'x'8744'y_50 (coe du_isJoinSemilattice_358 (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.∧-greatest
d_'8743''45'greatest_808 ::
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
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_808 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 v11
  = du_'8743''45'greatest_808 v11
du_'8743''45'greatest_808 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_808 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (coe
               du_'8743''45'greatest_222
               (coe du_isMeetSemilattice_360 (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.∨-least
d_'8744''45'least_810 ::
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
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_810 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11
  = du_'8744''45'least_810 v11
du_'8744''45'least_810 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_810 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (coe
               du_'8744''45'least_64 (coe du_isJoinSemilattice_358 (coe v3)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.∼-resp-≈
d_'8764''45'resp'45''8776'_812 ::
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
  T_IsBooleanAlgebra_730 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_812 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_'8764''45'resp'45''8776'_812 v11
du_'8764''45'resp'45''8776'_812 ::
  T_IsBooleanAlgebra_730 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_812 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_352 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_814 ::
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
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_814 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8764''45'resp'691''45''8776'_814 v11
du_'8764''45'resp'691''45''8776'_814 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_814 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_352 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_816 ::
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
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_816 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8764''45'resp'737''45''8776'_816 v11
du_'8764''45'resp'737''45''8776'_816 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_816 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_352 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.≲-resp-≈
d_'8818''45'resp'45''8776'_818 ::
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
  T_IsBooleanAlgebra_730 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_818 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                               ~v9 ~v10 v11
  = du_'8818''45'resp'45''8776'_818 v11
du_'8818''45'resp'45''8776'_818 ::
  T_IsBooleanAlgebra_730 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_818 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_352 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_820 ::
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
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_820 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8818''45'resp'691''45''8776'_820 v11
du_'8818''45'resp'691''45''8776'_820 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_820 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_352 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_822 ::
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
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_822 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11
  = du_'8818''45'resp'737''45''8776'_822 v11
du_'8818''45'resp'737''45''8776'_822 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_822 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_352 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.Eq.isPartialEquivalence
d_isPartialEquivalence_826 ::
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
  T_IsBooleanAlgebra_730 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_826 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11
  = du_isPartialEquivalence_826 v11
du_isPartialEquivalence_826 ::
  T_IsBooleanAlgebra_730 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_826 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_352 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                        (coe v5)))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.Eq.refl
d_refl_828 :: T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny
d_refl_828 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_352
               (coe
                  d_isLattice_518
                  (coe
                     d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0)))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.Eq.reflexive
d_reflexive_830 ::
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
  T_IsBooleanAlgebra_730 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_830 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_reflexive_830 v11
du_reflexive_830 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_830 v0
  = let v1 = d_isHeytingAlgebra_756 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_614 (coe v1) in
       coe
         (let v3 = d_isLattice_518 (coe v2) in
          coe
            (let v4 = d_isPartialOrder_352 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                          (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                       (coe
                          MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                          (coe v5))
                       v6)))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.Eq.sym
d_sym_832 ::
  T_IsBooleanAlgebra_730 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_832 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_352
               (coe
                  d_isLattice_518
                  (coe
                     d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0)))))))
-- Relation.Binary.Lattice.Structures.IsBooleanAlgebra._.Eq.trans
d_trans_834 ::
  T_IsBooleanAlgebra_730 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_834 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               d_isPartialOrder_352
               (coe
                  d_isLattice_518
                  (coe
                     d_isBoundedLattice_614 (coe d_isHeytingAlgebra_756 (coe v0)))))))
