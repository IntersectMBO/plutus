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

module MAlonzo.Code.Relation.Binary.Lattice.Bundles where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Lattice.Structures
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Relation.Binary.Lattice.Bundles.JoinSemilattice
d_JoinSemilattice_14 a0 a1 a2 = ()
data T_JoinSemilattice_14
  = C_constructor_96 (AgdaAny -> AgdaAny -> AgdaAny)
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
-- Relation.Binary.Lattice.Bundles.JoinSemilattice.Carrier
d_Carrier_32 :: T_JoinSemilattice_14 -> ()
d_Carrier_32 = erased
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._≈_
d__'8776'__34 :: T_JoinSemilattice_14 -> AgdaAny -> AgdaAny -> ()
d__'8776'__34 = erased
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._≤_
d__'8804'__36 :: T_JoinSemilattice_14 -> AgdaAny -> AgdaAny -> ()
d__'8804'__36 = erased
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._∨_
d__'8744'__38 ::
  T_JoinSemilattice_14 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__38 v0
  = case coe v0 of
      C_constructor_96 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.JoinSemilattice.isJoinSemilattice
d_isJoinSemilattice_40 ::
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_isJoinSemilattice_40 v0
  = case coe v0 of
      C_constructor_96 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.antisym
d_antisym_44 ::
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_44 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
         (coe d_isJoinSemilattice_40 (coe v0)))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.isEquivalence
d_isEquivalence_46 ::
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_46 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
            (coe d_isJoinSemilattice_40 (coe v0))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.isPartialOrder
d_isPartialOrder_48 ::
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_48 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
      (coe d_isJoinSemilattice_40 (coe v0))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.isPreorder
d_isPreorder_50 ::
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_50 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
         (coe d_isJoinSemilattice_40 (coe v0)))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.refl
d_refl_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 -> AgdaAny -> AgdaAny
d_refl_52 ~v0 ~v1 ~v2 v3 = du_refl_52 v3
du_refl_52 :: T_JoinSemilattice_14 -> AgdaAny -> AgdaAny
du_refl_52 v0
  = let v1 = d_isJoinSemilattice_40 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.reflexive
d_reflexive_54 ::
  T_JoinSemilattice_14 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_54 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
            (coe d_isJoinSemilattice_40 (coe v0))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.supremum
d_supremum_56 ::
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_56 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_supremum_32
      (coe d_isJoinSemilattice_40 (coe v0))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.trans
d_trans_58 ::
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_58 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
            (coe d_isJoinSemilattice_40 (coe v0))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.x≤x∨y
d_x'8804'x'8744'y_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_60 ~v0 ~v1 ~v2 v3 = du_x'8804'x'8744'y_60 v3
du_x'8804'x'8744'y_60 ::
  T_JoinSemilattice_14 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_60 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
      (coe d_isJoinSemilattice_40 (coe v0))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.y≤x∨y
d_y'8804'x'8744'y_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_62 ~v0 ~v1 ~v2 v3 = du_y'8804'x'8744'y_62 v3
du_y'8804'x'8744'y_62 ::
  T_JoinSemilattice_14 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_62 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
      (coe d_isJoinSemilattice_40 (coe v0))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.∨-least
d_'8744''45'least_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_64 ~v0 ~v1 ~v2 v3 = du_'8744''45'least_64 v3
du_'8744''45'least_64 ::
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_64 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
      (coe d_isJoinSemilattice_40 (coe v0))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_66 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_66 v3
du_'8764''45'resp'45''8776'_66 ::
  T_JoinSemilattice_14 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_66 v0
  = let v1 = d_isJoinSemilattice_40 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_68 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_68 v3
du_'8764''45'resp'691''45''8776'_68 ::
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_68 v0
  = let v1 = d_isJoinSemilattice_40 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_70 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_70 v3
du_'8764''45'resp'737''45''8776'_70 ::
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_70 v0
  = let v1 = d_isJoinSemilattice_40 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_72 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_72 v3
du_'8818''45'resp'45''8776'_72 ::
  T_JoinSemilattice_14 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_72 v0
  = let v1 = d_isJoinSemilattice_40 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_74 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_74 v3
du_'8818''45'resp'691''45''8776'_74 ::
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_74 v0
  = let v1 = d_isJoinSemilattice_40 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_76 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_76 v3
du_'8818''45'resp'737''45''8776'_76 ::
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_76 v0
  = let v1 = d_isJoinSemilattice_40 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_80 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_80 v3
du_isPartialEquivalence_80 ::
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_80 v0
  = let v1 = d_isJoinSemilattice_40 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                 (coe v1) in
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
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.Eq.refl
d_refl_82 :: T_JoinSemilattice_14 -> AgdaAny -> AgdaAny
d_refl_82 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
               (coe d_isJoinSemilattice_40 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.Eq.reflexive
d_reflexive_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_84 ~v0 ~v1 ~v2 v3 = du_reflexive_84 v3
du_reflexive_84 ::
  T_JoinSemilattice_14 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_84 v0
  = let v1 = d_isJoinSemilattice_40 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                 (coe v1) in
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
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.Eq.sym
d_sym_86 ::
  T_JoinSemilattice_14 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_86 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
               (coe d_isJoinSemilattice_40 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.Eq.trans
d_trans_88 ::
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_88 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
               (coe d_isJoinSemilattice_40 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice.poset
d_poset_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_90 ~v0 ~v1 ~v2 v3 = du_poset_90 v3
du_poset_90 ::
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_90 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
         (coe d_isJoinSemilattice_40 (coe v0)))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.preorder
d_preorder_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_preorder_94 ~v0 ~v1 ~v2 v3 = du_preorder_94 v3
du_preorder_94 ::
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_preorder_94 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522
      (coe du_poset_90 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice
d_BoundedJoinSemilattice_104 a0 a1 a2 = ()
data T_BoundedJoinSemilattice_104
  = C_constructor_196 (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny
                      MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_118
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice.Carrier
d_Carrier_124 :: T_BoundedJoinSemilattice_104 -> ()
d_Carrier_124 = erased
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._≈_
d__'8776'__126 ::
  T_BoundedJoinSemilattice_104 -> AgdaAny -> AgdaAny -> ()
d__'8776'__126 = erased
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._≤_
d__'8804'__128 ::
  T_BoundedJoinSemilattice_104 -> AgdaAny -> AgdaAny -> ()
d__'8804'__128 = erased
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._∨_
d__'8744'__130 ::
  T_BoundedJoinSemilattice_104 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__130 v0
  = case coe v0 of
      C_constructor_196 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice.⊥
d_'8869'_132 :: T_BoundedJoinSemilattice_104 -> AgdaAny
d_'8869'_132 v0
  = case coe v0 of
      C_constructor_196 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_134 ::
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_118
d_isBoundedJoinSemilattice_134 v0
  = case coe v0 of
      C_constructor_196 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.antisym
d_antisym_138 ::
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_138 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
            (coe d_isBoundedJoinSemilattice_134 (coe v0))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.isEquivalence
d_isEquivalence_140 ::
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_140 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
               (coe d_isBoundedJoinSemilattice_134 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.isJoinSemilattice
d_isJoinSemilattice_142 ::
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_isJoinSemilattice_142 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
      (coe d_isBoundedJoinSemilattice_134 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.isPartialOrder
d_isPartialOrder_144 ::
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_144 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
         (coe d_isBoundedJoinSemilattice_134 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.isPreorder
d_isPreorder_146 ::
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_146 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
            (coe d_isBoundedJoinSemilattice_134 (coe v0))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.minimum
d_minimum_148 :: T_BoundedJoinSemilattice_104 -> AgdaAny -> AgdaAny
d_minimum_148 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_minimum_130
      (coe d_isBoundedJoinSemilattice_134 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.refl
d_refl_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 -> AgdaAny -> AgdaAny
d_refl_150 ~v0 ~v1 ~v2 v3 = du_refl_150 v3
du_refl_150 :: T_BoundedJoinSemilattice_104 -> AgdaAny -> AgdaAny
du_refl_150 v0
  = let v1 = d_isBoundedJoinSemilattice_134 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_104
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.reflexive
d_reflexive_152 ::
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_152 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
               (coe d_isBoundedJoinSemilattice_134 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.supremum
d_supremum_154 ::
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_154 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_supremum_32
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
         (coe d_isBoundedJoinSemilattice_134 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.trans
d_trans_156 ::
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_156 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
               (coe d_isBoundedJoinSemilattice_134 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.x≤x∨y
d_x'8804'x'8744'y_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_158 ~v0 ~v1 ~v2 v3 = du_x'8804'x'8744'y_158 v3
du_x'8804'x'8744'y_158 ::
  T_BoundedJoinSemilattice_104 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_158 v0
  = let v1 = d_isBoundedJoinSemilattice_134 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.y≤x∨y
d_y'8804'x'8744'y_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_160 ~v0 ~v1 ~v2 v3 = du_y'8804'x'8744'y_160 v3
du_y'8804'x'8744'y_160 ::
  T_BoundedJoinSemilattice_104 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_160 v0
  = let v1 = d_isBoundedJoinSemilattice_134 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.∨-least
d_'8744''45'least_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_162 ~v0 ~v1 ~v2 v3 = du_'8744''45'least_162 v3
du_'8744''45'least_162 ::
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_162 v0
  = let v1 = d_isBoundedJoinSemilattice_134 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_164 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_164 v3
du_'8764''45'resp'45''8776'_164 ::
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_164 v0
  = let v1 = d_isBoundedJoinSemilattice_134 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_166 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_166 v3
du_'8764''45'resp'691''45''8776'_166 ::
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_166 v0
  = let v1 = d_isBoundedJoinSemilattice_134 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_168 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_168 v3
du_'8764''45'resp'737''45''8776'_168 ::
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_168 v0
  = let v1 = d_isBoundedJoinSemilattice_134 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_170 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_170 v3
du_'8818''45'resp'45''8776'_170 ::
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_170 v0
  = let v1 = d_isBoundedJoinSemilattice_134 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_172 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_172 v3
du_'8818''45'resp'691''45''8776'_172 ::
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_172 v0
  = let v1 = d_isBoundedJoinSemilattice_134 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_174 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_174 v3
du_'8818''45'resp'737''45''8776'_174 ::
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_174 v0
  = let v1 = d_isBoundedJoinSemilattice_134 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_178 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_178 v3
du_isPartialEquivalence_178 ::
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_178 v0
  = let v1 = d_isBoundedJoinSemilattice_134 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.Eq.refl
d_refl_180 :: T_BoundedJoinSemilattice_104 -> AgdaAny -> AgdaAny
d_refl_180 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
                  (coe d_isBoundedJoinSemilattice_134 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.Eq.reflexive
d_reflexive_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_182 ~v0 ~v1 ~v2 v3 = du_reflexive_182 v3
du_reflexive_182 ::
  T_BoundedJoinSemilattice_104 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_182 v0
  = let v1 = d_isBoundedJoinSemilattice_134 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.Eq.sym
d_sym_184 ::
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_184 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
                  (coe d_isBoundedJoinSemilattice_134 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.Eq.trans
d_trans_186 ::
  T_BoundedJoinSemilattice_104 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_186 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
                  (coe d_isBoundedJoinSemilattice_134 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice.joinSemilattice
d_joinSemilattice_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 -> T_JoinSemilattice_14
d_joinSemilattice_188 ~v0 ~v1 ~v2 v3 = du_joinSemilattice_188 v3
du_joinSemilattice_188 ::
  T_BoundedJoinSemilattice_104 -> T_JoinSemilattice_14
du_joinSemilattice_188 v0
  = coe
      C_constructor_96 (d__'8744'__130 (coe v0))
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_128
         (coe d_isBoundedJoinSemilattice_134 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.poset
d_poset_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_192 ~v0 ~v1 ~v2 v3 = du_poset_192 v3
du_poset_192 ::
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_192 v0
  = coe du_poset_90 (coe du_joinSemilattice_188 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.preorder
d_preorder_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_preorder_194 ~v0 ~v1 ~v2 v3 = du_preorder_194 v3
du_preorder_194 ::
  T_BoundedJoinSemilattice_104 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_preorder_194 v0
  = let v1 = coe du_joinSemilattice_188 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522
         (coe du_poset_90 (coe v1)))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice
d_MeetSemilattice_204 a0 a1 a2 = ()
data T_MeetSemilattice_204
  = C_constructor_286 (AgdaAny -> AgdaAny -> AgdaAny)
                      MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
-- Relation.Binary.Lattice.Bundles.MeetSemilattice.Carrier
d_Carrier_222 :: T_MeetSemilattice_204 -> ()
d_Carrier_222 = erased
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._≈_
d__'8776'__224 :: T_MeetSemilattice_204 -> AgdaAny -> AgdaAny -> ()
d__'8776'__224 = erased
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._≤_
d__'8804'__226 :: T_MeetSemilattice_204 -> AgdaAny -> AgdaAny -> ()
d__'8804'__226 = erased
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._∧_
d__'8743'__228 ::
  T_MeetSemilattice_204 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__228 v0
  = case coe v0 of
      C_constructor_286 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.MeetSemilattice.isMeetSemilattice
d_isMeetSemilattice_230 ::
  T_MeetSemilattice_204 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
d_isMeetSemilattice_230 v0
  = case coe v0 of
      C_constructor_286 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.antisym
d_antisym_234 ::
  T_MeetSemilattice_204 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_234 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
         (coe d_isMeetSemilattice_230 (coe v0)))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.infimum
d_infimum_236 ::
  T_MeetSemilattice_204 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_236 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_infimum_194
      (coe d_isMeetSemilattice_230 (coe v0))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.isEquivalence
d_isEquivalence_238 ::
  T_MeetSemilattice_204 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_238 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
            (coe d_isMeetSemilattice_230 (coe v0))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.isPartialOrder
d_isPartialOrder_240 ::
  T_MeetSemilattice_204 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_240 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
      (coe d_isMeetSemilattice_230 (coe v0))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.isPreorder
d_isPreorder_242 ::
  T_MeetSemilattice_204 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_242 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
         (coe d_isMeetSemilattice_230 (coe v0)))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.refl
d_refl_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_204 -> AgdaAny -> AgdaAny
d_refl_244 ~v0 ~v1 ~v2 v3 = du_refl_244 v3
du_refl_244 :: T_MeetSemilattice_204 -> AgdaAny -> AgdaAny
du_refl_244 v0
  = let v1 = d_isMeetSemilattice_230 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.reflexive
d_reflexive_246 ::
  T_MeetSemilattice_204 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_246 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
            (coe d_isMeetSemilattice_230 (coe v0))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.trans
d_trans_248 ::
  T_MeetSemilattice_204 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_248 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
            (coe d_isMeetSemilattice_230 (coe v0))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.x∧y≤x
d_x'8743'y'8804'x_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_204 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_250 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'x_250 v3
du_x'8743'y'8804'x_250 ::
  T_MeetSemilattice_204 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_250 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'x_200
      (coe d_isMeetSemilattice_230 (coe v0))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.x∧y≤y
d_x'8743'y'8804'y_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_204 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_252 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'y_252 v3
du_x'8743'y'8804'y_252 ::
  T_MeetSemilattice_204 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_252 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'y_212
      (coe d_isMeetSemilattice_230 (coe v0))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.∧-greatest
d_'8743''45'greatest_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_204 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_254 ~v0 ~v1 ~v2 v3
  = du_'8743''45'greatest_254 v3
du_'8743''45'greatest_254 ::
  T_MeetSemilattice_204 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_254 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8743''45'greatest_226
      (coe d_isMeetSemilattice_230 (coe v0))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_204 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_256 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_256 v3
du_'8764''45'resp'45''8776'_256 ::
  T_MeetSemilattice_204 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_256 v0
  = let v1 = d_isMeetSemilattice_230 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_204 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_258 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_258 v3
du_'8764''45'resp'691''45''8776'_258 ::
  T_MeetSemilattice_204 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_258 v0
  = let v1 = d_isMeetSemilattice_230 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_204 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_260 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_260 v3
du_'8764''45'resp'737''45''8776'_260 ::
  T_MeetSemilattice_204 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_260 v0
  = let v1 = d_isMeetSemilattice_230 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_204 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_262 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_262 v3
du_'8818''45'resp'45''8776'_262 ::
  T_MeetSemilattice_204 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_262 v0
  = let v1 = d_isMeetSemilattice_230 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_204 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_264 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_264 v3
du_'8818''45'resp'691''45''8776'_264 ::
  T_MeetSemilattice_204 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_264 v0
  = let v1 = d_isMeetSemilattice_230 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_204 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_266 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_266 v3
du_'8818''45'resp'737''45''8776'_266 ::
  T_MeetSemilattice_204 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_266 v0
  = let v1 = d_isMeetSemilattice_230 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_204 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_270 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_270 v3
du_isPartialEquivalence_270 ::
  T_MeetSemilattice_204 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_270 v0
  = let v1 = d_isMeetSemilattice_230 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                 (coe v1) in
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
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.Eq.refl
d_refl_272 :: T_MeetSemilattice_204 -> AgdaAny -> AgdaAny
d_refl_272 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
               (coe d_isMeetSemilattice_230 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.Eq.reflexive
d_reflexive_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_204 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_274 ~v0 ~v1 ~v2 v3 = du_reflexive_274 v3
du_reflexive_274 ::
  T_MeetSemilattice_204 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_274 v0
  = let v1 = d_isMeetSemilattice_230 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                 (coe v1) in
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
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.Eq.sym
d_sym_276 ::
  T_MeetSemilattice_204 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_276 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
               (coe d_isMeetSemilattice_230 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.Eq.trans
d_trans_278 ::
  T_MeetSemilattice_204 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_278 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
               (coe d_isMeetSemilattice_230 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice.poset
d_poset_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_204 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_280 ~v0 ~v1 ~v2 v3 = du_poset_280 v3
du_poset_280 ::
  T_MeetSemilattice_204 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_280 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
         (coe d_isMeetSemilattice_230 (coe v0)))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.preorder
d_preorder_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_204 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_preorder_284 ~v0 ~v1 ~v2 v3 = du_preorder_284 v3
du_preorder_284 ::
  T_MeetSemilattice_204 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_preorder_284 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522
      (coe du_poset_280 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice
d_BoundedMeetSemilattice_294 a0 a1 a2 = ()
data T_BoundedMeetSemilattice_294
  = C_constructor_386 (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny
                      MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_280
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice.Carrier
d_Carrier_314 :: T_BoundedMeetSemilattice_294 -> ()
d_Carrier_314 = erased
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._≈_
d__'8776'__316 ::
  T_BoundedMeetSemilattice_294 -> AgdaAny -> AgdaAny -> ()
d__'8776'__316 = erased
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._≤_
d__'8804'__318 ::
  T_BoundedMeetSemilattice_294 -> AgdaAny -> AgdaAny -> ()
d__'8804'__318 = erased
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._∧_
d__'8743'__320 ::
  T_BoundedMeetSemilattice_294 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__320 v0
  = case coe v0 of
      C_constructor_386 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice.⊤
d_'8868'_322 :: T_BoundedMeetSemilattice_294 -> AgdaAny
d_'8868'_322 v0
  = case coe v0 of
      C_constructor_386 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_324 ::
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_280
d_isBoundedMeetSemilattice_324 v0
  = case coe v0 of
      C_constructor_386 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.antisym
d_antisym_328 ::
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_328 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
            (coe d_isBoundedMeetSemilattice_324 (coe v0))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.infimum
d_infimum_330 ::
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_330 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_infimum_194
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
         (coe d_isBoundedMeetSemilattice_324 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.isEquivalence
d_isEquivalence_332 ::
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_332 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
               (coe d_isBoundedMeetSemilattice_324 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.isMeetSemilattice
d_isMeetSemilattice_334 ::
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
d_isMeetSemilattice_334 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
      (coe d_isBoundedMeetSemilattice_324 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.isPartialOrder
d_isPartialOrder_336 ::
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_336 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
         (coe d_isBoundedMeetSemilattice_324 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.isPreorder
d_isPreorder_338 ::
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_338 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
            (coe d_isBoundedMeetSemilattice_324 (coe v0))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.maximum
d_maximum_340 :: T_BoundedMeetSemilattice_294 -> AgdaAny -> AgdaAny
d_maximum_340 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_maximum_292
      (coe d_isBoundedMeetSemilattice_324 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.refl
d_refl_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 -> AgdaAny -> AgdaAny
d_refl_342 ~v0 ~v1 ~v2 v3 = du_refl_342 v3
du_refl_342 :: T_BoundedMeetSemilattice_294 -> AgdaAny -> AgdaAny
du_refl_342 v0
  = let v1 = d_isBoundedMeetSemilattice_324 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_104
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.reflexive
d_reflexive_344 ::
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_344 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
               (coe d_isBoundedMeetSemilattice_324 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.trans
d_trans_346 ::
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_346 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
               (coe d_isBoundedMeetSemilattice_324 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.x∧y≤x
d_x'8743'y'8804'x_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_348 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'x_348 v3
du_x'8743'y'8804'x_348 ::
  T_BoundedMeetSemilattice_294 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_348 v0
  = let v1 = d_isBoundedMeetSemilattice_324 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'x_200
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.x∧y≤y
d_x'8743'y'8804'y_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_350 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'y_350 v3
du_x'8743'y'8804'y_350 ::
  T_BoundedMeetSemilattice_294 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_350 v0
  = let v1 = d_isBoundedMeetSemilattice_324 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'y_212
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.∧-greatest
d_'8743''45'greatest_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_352 ~v0 ~v1 ~v2 v3
  = du_'8743''45'greatest_352 v3
du_'8743''45'greatest_352 ::
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_352 v0
  = let v1 = d_isBoundedMeetSemilattice_324 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8743''45'greatest_226
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_354 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_354 v3
du_'8764''45'resp'45''8776'_354 ::
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_354 v0
  = let v1 = d_isBoundedMeetSemilattice_324 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_356 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_356 v3
du_'8764''45'resp'691''45''8776'_356 ::
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_356 v0
  = let v1 = d_isBoundedMeetSemilattice_324 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_358 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_358 v3
du_'8764''45'resp'737''45''8776'_358 ::
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_358 v0
  = let v1 = d_isBoundedMeetSemilattice_324 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_360 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_360 v3
du_'8818''45'resp'45''8776'_360 ::
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_360 v0
  = let v1 = d_isBoundedMeetSemilattice_324 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_362 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_362 v3
du_'8818''45'resp'691''45''8776'_362 ::
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_362 v0
  = let v1 = d_isBoundedMeetSemilattice_324 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_364 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_364 v3
du_'8818''45'resp'737''45''8776'_364 ::
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_364 v0
  = let v1 = d_isBoundedMeetSemilattice_324 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_368 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_368 v3
du_isPartialEquivalence_368 ::
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_368 v0
  = let v1 = d_isBoundedMeetSemilattice_324 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.Eq.refl
d_refl_370 :: T_BoundedMeetSemilattice_294 -> AgdaAny -> AgdaAny
d_refl_370 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
                  (coe d_isBoundedMeetSemilattice_324 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.Eq.reflexive
d_reflexive_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_372 ~v0 ~v1 ~v2 v3 = du_reflexive_372 v3
du_reflexive_372 ::
  T_BoundedMeetSemilattice_294 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_372 v0
  = let v1 = d_isBoundedMeetSemilattice_324 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.Eq.sym
d_sym_374 ::
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_374 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
                  (coe d_isBoundedMeetSemilattice_324 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.Eq.trans
d_trans_376 ::
  T_BoundedMeetSemilattice_294 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_376 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_192
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
                  (coe d_isBoundedMeetSemilattice_324 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice.meetSemilattice
d_meetSemilattice_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 -> T_MeetSemilattice_204
d_meetSemilattice_378 ~v0 ~v1 ~v2 v3 = du_meetSemilattice_378 v3
du_meetSemilattice_378 ::
  T_BoundedMeetSemilattice_294 -> T_MeetSemilattice_204
du_meetSemilattice_378 v0
  = coe
      C_constructor_286 (d__'8743'__320 (coe v0))
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_290
         (coe d_isBoundedMeetSemilattice_324 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.poset
d_poset_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_382 ~v0 ~v1 ~v2 v3 = du_poset_382 v3
du_poset_382 ::
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_382 v0
  = coe du_poset_280 (coe du_meetSemilattice_378 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.preorder
d_preorder_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_preorder_384 ~v0 ~v1 ~v2 v3 = du_preorder_384 v3
du_preorder_384 ::
  T_BoundedMeetSemilattice_294 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_preorder_384 v0
  = let v1 = coe du_meetSemilattice_378 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522
         (coe du_poset_280 (coe v1)))
-- Relation.Binary.Lattice.Bundles.Lattice
d_Lattice_394 a0 a1 a2 = ()
data T_Lattice_394
  = C_constructor_498 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny)
                      MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_348
-- Relation.Binary.Lattice.Bundles.Lattice.Carrier
d_Carrier_414 :: T_Lattice_394 -> ()
d_Carrier_414 = erased
-- Relation.Binary.Lattice.Bundles.Lattice._≈_
d__'8776'__416 :: T_Lattice_394 -> AgdaAny -> AgdaAny -> ()
d__'8776'__416 = erased
-- Relation.Binary.Lattice.Bundles.Lattice._≤_
d__'8804'__418 :: T_Lattice_394 -> AgdaAny -> AgdaAny -> ()
d__'8804'__418 = erased
-- Relation.Binary.Lattice.Bundles.Lattice._∨_
d__'8744'__420 :: T_Lattice_394 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__420 v0
  = case coe v0 of
      C_constructor_498 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.Lattice._∧_
d__'8743'__422 :: T_Lattice_394 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__422 v0
  = case coe v0 of
      C_constructor_498 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.Lattice.isLattice
d_isLattice_424 ::
  T_Lattice_394 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_348
d_isLattice_424 v0
  = case coe v0 of
      C_constructor_498 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.Lattice._.antisym
d_antisym_428 ::
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_428 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
         (coe d_isLattice_424 (coe v0)))
-- Relation.Binary.Lattice.Bundles.Lattice._.infimum
d_infimum_430 ::
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_430 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_infimum_364
      (coe d_isLattice_424 (coe v0))
-- Relation.Binary.Lattice.Bundles.Lattice._.isEquivalence
d_isEquivalence_432 ::
  T_Lattice_394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_432 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
            (coe d_isLattice_424 (coe v0))))
-- Relation.Binary.Lattice.Bundles.Lattice._.isJoinSemilattice
d_isJoinSemilattice_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_isJoinSemilattice_434 ~v0 ~v1 ~v2 v3
  = du_isJoinSemilattice_434 v3
du_isJoinSemilattice_434 ::
  T_Lattice_394 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_isJoinSemilattice_434 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
      (coe d_isLattice_424 (coe v0))
-- Relation.Binary.Lattice.Bundles.Lattice._.isMeetSemilattice
d_isMeetSemilattice_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
d_isMeetSemilattice_436 ~v0 ~v1 ~v2 v3
  = du_isMeetSemilattice_436 v3
du_isMeetSemilattice_436 ::
  T_Lattice_394 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
du_isMeetSemilattice_436 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
      (coe d_isLattice_424 (coe v0))
-- Relation.Binary.Lattice.Bundles.Lattice._.isPartialOrder
d_isPartialOrder_438 ::
  T_Lattice_394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_438 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
      (coe d_isLattice_424 (coe v0))
-- Relation.Binary.Lattice.Bundles.Lattice._.isPreorder
d_isPreorder_440 ::
  T_Lattice_394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_440 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
         (coe d_isLattice_424 (coe v0)))
-- Relation.Binary.Lattice.Bundles.Lattice._.refl
d_refl_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 -> AgdaAny -> AgdaAny
d_refl_442 ~v0 ~v1 ~v2 v3 = du_refl_442 v3
du_refl_442 :: T_Lattice_394 -> AgdaAny -> AgdaAny
du_refl_442 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_104
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.Lattice._.reflexive
d_reflexive_444 ::
  T_Lattice_394 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_444 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
            (coe d_isLattice_424 (coe v0))))
-- Relation.Binary.Lattice.Bundles.Lattice._.supremum
d_supremum_446 ::
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_446 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_supremum_362
      (coe d_isLattice_424 (coe v0))
-- Relation.Binary.Lattice.Bundles.Lattice._.trans
d_trans_448 ::
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_448 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
            (coe d_isLattice_424 (coe v0))))
-- Relation.Binary.Lattice.Bundles.Lattice._.x∧y≤x
d_x'8743'y'8804'x_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_450 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'x_450 v3
du_x'8743'y'8804'x_450 ::
  T_Lattice_394 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_450 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'x_200
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.Lattice._.x∧y≤y
d_x'8743'y'8804'y_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_452 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'y_452 v3
du_x'8743'y'8804'y_452 ::
  T_Lattice_394 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_452 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'y_212
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.Lattice._.x≤x∨y
d_x'8804'x'8744'y_454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_454 ~v0 ~v1 ~v2 v3 = du_x'8804'x'8744'y_454 v3
du_x'8804'x'8744'y_454 ::
  T_Lattice_394 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_454 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.Lattice._.y≤x∨y
d_y'8804'x'8744'y_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_456 ~v0 ~v1 ~v2 v3 = du_y'8804'x'8744'y_456 v3
du_y'8804'x'8744'y_456 ::
  T_Lattice_394 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_456 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.Lattice._.∧-greatest
d_'8743''45'greatest_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_458 ~v0 ~v1 ~v2 v3
  = du_'8743''45'greatest_458 v3
du_'8743''45'greatest_458 ::
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_458 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8743''45'greatest_226
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.Lattice._.∨-least
d_'8744''45'least_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_460 ~v0 ~v1 ~v2 v3 = du_'8744''45'least_460 v3
du_'8744''45'least_460 ::
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_460 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.Lattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_462 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_462 v3
du_'8764''45'resp'45''8776'_462 ::
  T_Lattice_394 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_462 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.Lattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_464 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_464 v3
du_'8764''45'resp'691''45''8776'_464 ::
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_464 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.Lattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_466 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_466 v3
du_'8764''45'resp'737''45''8776'_466 ::
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_466 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.Lattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_468 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_468 v3
du_'8818''45'resp'45''8776'_468 ::
  T_Lattice_394 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_468 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.Lattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_470 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_470 v3
du_'8818''45'resp'691''45''8776'_470 ::
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_470 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.Lattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_472 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_472 v3
du_'8818''45'resp'737''45''8776'_472 ::
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_472 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.Lattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_476 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_476 v3
du_isPartialEquivalence_476 ::
  T_Lattice_394 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_476 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                 (coe v1) in
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
-- Relation.Binary.Lattice.Bundles.Lattice._.Eq.refl
d_refl_478 :: T_Lattice_394 -> AgdaAny -> AgdaAny
d_refl_478 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe d_isLattice_424 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.Lattice._.Eq.reflexive
d_reflexive_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_480 ~v0 ~v1 ~v2 v3 = du_reflexive_480 v3
du_reflexive_480 ::
  T_Lattice_394 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_480 v0
  = let v1 = d_isLattice_424 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                 (coe v1) in
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
-- Relation.Binary.Lattice.Bundles.Lattice._.Eq.sym
d_sym_482 ::
  T_Lattice_394 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_482 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe d_isLattice_424 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.Lattice._.Eq.trans
d_trans_484 ::
  T_Lattice_394 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_484 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe d_isLattice_424 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.Lattice.setoid
d_setoid_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_486 ~v0 ~v1 ~v2 v3 = du_setoid_486 v3
du_setoid_486 ::
  T_Lattice_394 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_486 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe d_isLattice_424 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.Lattice.joinSemilattice
d_joinSemilattice_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 -> T_JoinSemilattice_14
d_joinSemilattice_488 ~v0 ~v1 ~v2 v3 = du_joinSemilattice_488 v3
du_joinSemilattice_488 :: T_Lattice_394 -> T_JoinSemilattice_14
du_joinSemilattice_488 v0
  = coe
      C_constructor_96 (d__'8744'__420 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
         (coe d_isLattice_424 (coe v0)))
-- Relation.Binary.Lattice.Bundles.Lattice.meetSemilattice
d_meetSemilattice_490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 -> T_MeetSemilattice_204
d_meetSemilattice_490 ~v0 ~v1 ~v2 v3 = du_meetSemilattice_490 v3
du_meetSemilattice_490 :: T_Lattice_394 -> T_MeetSemilattice_204
du_meetSemilattice_490 v0
  = coe
      C_constructor_286 (d__'8743'__422 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
         (coe d_isLattice_424 (coe v0)))
-- Relation.Binary.Lattice.Bundles.Lattice._.poset
d_poset_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 -> MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_494 ~v0 ~v1 ~v2 v3 = du_poset_494 v3
du_poset_494 ::
  T_Lattice_394 -> MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_494 v0
  = coe du_poset_90 (coe du_joinSemilattice_488 (coe v0))
-- Relation.Binary.Lattice.Bundles.Lattice._.preorder
d_preorder_496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_394 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_preorder_496 ~v0 ~v1 ~v2 v3 = du_preorder_496 v3
du_preorder_496 ::
  T_Lattice_394 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_preorder_496 v0
  = let v1 = coe du_joinSemilattice_488 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522
         (coe du_poset_90 (coe v1)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice
d_DistributiveLattice_506 a0 a1 a2 = ()
data T_DistributiveLattice_506
  = C_constructor_620 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny)
                      MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsDistributiveLattice_430
-- Relation.Binary.Lattice.Bundles.DistributiveLattice.Carrier
d_Carrier_526 :: T_DistributiveLattice_506 -> ()
d_Carrier_526 = erased
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._≈_
d__'8776'__528 ::
  T_DistributiveLattice_506 -> AgdaAny -> AgdaAny -> ()
d__'8776'__528 = erased
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._≤_
d__'8804'__530 ::
  T_DistributiveLattice_506 -> AgdaAny -> AgdaAny -> ()
d__'8804'__530 = erased
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._∨_
d__'8744'__532 ::
  T_DistributiveLattice_506 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__532 v0
  = case coe v0 of
      C_constructor_620 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._∧_
d__'8743'__534 ::
  T_DistributiveLattice_506 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__534 v0
  = case coe v0 of
      C_constructor_620 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.DistributiveLattice.isDistributiveLattice
d_isDistributiveLattice_536 ::
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsDistributiveLattice_430
d_isDistributiveLattice_536 v0
  = case coe v0 of
      C_constructor_620 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_540 ::
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8744'_540 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_'8743''45'distrib'737''45''8744'_442
      (coe d_isDistributiveLattice_536 (coe v0))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice.lattice
d_lattice_546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 -> T_Lattice_394
d_lattice_546 ~v0 ~v1 ~v2 v3 = du_lattice_546 v3
du_lattice_546 :: T_DistributiveLattice_506 -> T_Lattice_394
du_lattice_546 v0
  = coe
      C_constructor_498 (d__'8744'__532 (coe v0))
      (d__'8743'__534 (coe v0))
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_440
         (coe d_isDistributiveLattice_536 (coe v0)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.antisym
d_antisym_550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_550 ~v0 ~v1 ~v2 v3 = du_antisym_550 v3
du_antisym_550 ::
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_550 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_440
            (coe d_isDistributiveLattice_536 (coe v0))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.infimum
d_infimum_552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_552 ~v0 ~v1 ~v2 v3 = du_infimum_552 v3
du_infimum_552 ::
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infimum_552 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_infimum_364
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_440
         (coe d_isDistributiveLattice_536 (coe v0)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.isEquivalence
d_isEquivalence_554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_554 ~v0 ~v1 ~v2 v3 = du_isEquivalence_554 v3
du_isEquivalence_554 ::
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_554 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_440
               (coe d_isDistributiveLattice_536 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.isJoinSemilattice
d_isJoinSemilattice_556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_isJoinSemilattice_556 ~v0 ~v1 ~v2 v3
  = du_isJoinSemilattice_556 v3
du_isJoinSemilattice_556 ::
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_isJoinSemilattice_556 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
         (coe d_isLattice_424 (coe v1)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.isLattice
d_isLattice_558 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_348
d_isLattice_558 ~v0 ~v1 ~v2 v3 = du_isLattice_558 v3
du_isLattice_558 ::
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_348
du_isLattice_558 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_440
      (coe d_isDistributiveLattice_536 (coe v0))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.isMeetSemilattice
d_isMeetSemilattice_560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
d_isMeetSemilattice_560 ~v0 ~v1 ~v2 v3
  = du_isMeetSemilattice_560 v3
du_isMeetSemilattice_560 ::
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
du_isMeetSemilattice_560 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
         (coe d_isLattice_424 (coe v1)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.isPartialOrder
d_isPartialOrder_562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_562 ~v0 ~v1 ~v2 v3 = du_isPartialOrder_562 v3
du_isPartialOrder_562 ::
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_isPartialOrder_562 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_440
         (coe d_isDistributiveLattice_536 (coe v0)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.isPreorder
d_isPreorder_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_564 ~v0 ~v1 ~v2 v3 = du_isPreorder_564 v3
du_isPreorder_564 ::
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_isPreorder_564 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_440
            (coe d_isDistributiveLattice_536 (coe v0))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.joinSemilattice
d_joinSemilattice_566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 -> T_JoinSemilattice_14
d_joinSemilattice_566 ~v0 ~v1 ~v2 v3 = du_joinSemilattice_566 v3
du_joinSemilattice_566 ::
  T_DistributiveLattice_506 -> T_JoinSemilattice_14
du_joinSemilattice_566 v0
  = coe du_joinSemilattice_488 (coe du_lattice_546 (coe v0))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.meetSemilattice
d_meetSemilattice_568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 -> T_MeetSemilattice_204
d_meetSemilattice_568 ~v0 ~v1 ~v2 v3 = du_meetSemilattice_568 v3
du_meetSemilattice_568 ::
  T_DistributiveLattice_506 -> T_MeetSemilattice_204
du_meetSemilattice_568 v0
  = coe du_meetSemilattice_490 (coe du_lattice_546 (coe v0))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.poset
d_poset_570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_570 ~v0 ~v1 ~v2 v3 = du_poset_570 v3
du_poset_570 ::
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_570 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe (coe du_poset_90 (coe du_joinSemilattice_488 (coe v1)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.preorder
d_preorder_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_preorder_572 ~v0 ~v1 ~v2 v3 = du_preorder_572 v3
du_preorder_572 ::
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_preorder_572 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = coe du_joinSemilattice_488 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522
            (coe du_poset_90 (coe v2))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.refl
d_refl_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 -> AgdaAny -> AgdaAny
d_refl_574 ~v0 ~v1 ~v2 v3 = du_refl_574 v3
du_refl_574 :: T_DistributiveLattice_506 -> AgdaAny -> AgdaAny
du_refl_574 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_104
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.reflexive
d_reflexive_576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_576 ~v0 ~v1 ~v2 v3 = du_reflexive_576 v3
du_reflexive_576 ::
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_576 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_440
               (coe d_isDistributiveLattice_536 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.setoid
d_setoid_578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_578 ~v0 ~v1 ~v2 v3 = du_setoid_578 v3
du_setoid_578 ::
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_578 v0 = coe du_setoid_486 (coe du_lattice_546 (coe v0))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.supremum
d_supremum_580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_580 ~v0 ~v1 ~v2 v3 = du_supremum_580 v3
du_supremum_580 ::
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_supremum_580 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_supremum_362
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_440
         (coe d_isDistributiveLattice_536 (coe v0)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.trans
d_trans_582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_582 ~v0 ~v1 ~v2 v3 = du_trans_582 v3
du_trans_582 ::
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_582 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_440
               (coe d_isDistributiveLattice_536 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.x∧y≤x
d_x'8743'y'8804'x_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_584 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'x_584 v3
du_x'8743'y'8804'x_584 ::
  T_DistributiveLattice_506 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_584 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'x_200
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.x∧y≤y
d_x'8743'y'8804'y_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_586 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'y_586 v3
du_x'8743'y'8804'y_586 ::
  T_DistributiveLattice_506 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_586 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'y_212
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.x≤x∨y
d_x'8804'x'8744'y_588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_588 ~v0 ~v1 ~v2 v3 = du_x'8804'x'8744'y_588 v3
du_x'8804'x'8744'y_588 ::
  T_DistributiveLattice_506 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_588 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.y≤x∨y
d_y'8804'x'8744'y_590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_590 ~v0 ~v1 ~v2 v3 = du_y'8804'x'8744'y_590 v3
du_y'8804'x'8744'y_590 ::
  T_DistributiveLattice_506 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_590 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.∧-greatest
d_'8743''45'greatest_592 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_592 ~v0 ~v1 ~v2 v3
  = du_'8743''45'greatest_592 v3
du_'8743''45'greatest_592 ::
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_592 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8743''45'greatest_226
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.∨-least
d_'8744''45'least_594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_594 ~v0 ~v1 ~v2 v3 = du_'8744''45'least_594 v3
du_'8744''45'least_594 ::
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_594 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_596 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_596 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_596 v3
du_'8764''45'resp'45''8776'_596 ::
  T_DistributiveLattice_506 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_596 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_598 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_598 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_598 v3
du_'8764''45'resp'691''45''8776'_598 ::
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_598 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_600 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_600 v3
du_'8764''45'resp'737''45''8776'_600 ::
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_600 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_602 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_602 v3
du_'8818''45'resp'45''8776'_602 ::
  T_DistributiveLattice_506 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_602 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_604 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_604 v3
du_'8818''45'resp'691''45''8776'_604 ::
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_604 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_606 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_606 v3
du_'8818''45'resp'737''45''8776'_606 ::
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_606 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_610 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_610 v3
du_isPartialEquivalence_610 ::
  T_DistributiveLattice_506 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_610 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.Eq.refl
d_refl_612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 -> AgdaAny -> AgdaAny
d_refl_612 ~v0 ~v1 ~v2 v3 = du_refl_612 v3
du_refl_612 :: T_DistributiveLattice_506 -> AgdaAny -> AgdaAny
du_refl_612 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_440
                  (coe d_isDistributiveLattice_536 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.Eq.reflexive
d_reflexive_614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_614 ~v0 ~v1 ~v2 v3 = du_reflexive_614 v3
du_reflexive_614 ::
  T_DistributiveLattice_506 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_614 v0
  = let v1 = coe du_lattice_546 (coe v0) in
    coe
      (let v2 = d_isLattice_424 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.Eq.sym
d_sym_616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_616 ~v0 ~v1 ~v2 v3 = du_sym_616 v3
du_sym_616 ::
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_616 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_440
                  (coe d_isDistributiveLattice_536 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.Eq.trans
d_trans_618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_618 ~v0 ~v1 ~v2 v3 = du_trans_618 v3
du_trans_618 ::
  T_DistributiveLattice_506 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_618 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_440
                  (coe d_isDistributiveLattice_536 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice
d_BoundedLattice_628 a0 a1 a2 = ()
data T_BoundedLattice_628
  = C_constructor_756 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny AgdaAny
                      MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedLattice_514
-- Relation.Binary.Lattice.Bundles.BoundedLattice.Carrier
d_Carrier_652 :: T_BoundedLattice_628 -> ()
d_Carrier_652 = erased
-- Relation.Binary.Lattice.Bundles.BoundedLattice._≈_
d__'8776'__654 :: T_BoundedLattice_628 -> AgdaAny -> AgdaAny -> ()
d__'8776'__654 = erased
-- Relation.Binary.Lattice.Bundles.BoundedLattice._≤_
d__'8804'__656 :: T_BoundedLattice_628 -> AgdaAny -> AgdaAny -> ()
d__'8804'__656 = erased
-- Relation.Binary.Lattice.Bundles.BoundedLattice._∨_
d__'8744'__658 ::
  T_BoundedLattice_628 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__658 v0
  = case coe v0 of
      C_constructor_756 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedLattice._∧_
d__'8743'__660 ::
  T_BoundedLattice_628 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__660 v0
  = case coe v0 of
      C_constructor_756 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedLattice.⊤
d_'8868'_662 :: T_BoundedLattice_628 -> AgdaAny
d_'8868'_662 v0
  = case coe v0 of
      C_constructor_756 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedLattice.⊥
d_'8869'_664 :: T_BoundedLattice_628 -> AgdaAny
d_'8869'_664 v0
  = case coe v0 of
      C_constructor_756 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedLattice.isBoundedLattice
d_isBoundedLattice_666 ::
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedLattice_514
d_isBoundedLattice_666 v0
  = case coe v0 of
      C_constructor_756 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.antisym
d_antisym_670 ::
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_670 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
            (coe d_isBoundedLattice_666 (coe v0))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.infimum
d_infimum_672 ::
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_672 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_infimum_364
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
         (coe d_isBoundedLattice_666 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_674 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_118
d_isBoundedJoinSemilattice_674 ~v0 ~v1 ~v2 v3
  = du_isBoundedJoinSemilattice_674 v3
du_isBoundedJoinSemilattice_674 ::
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_118
du_isBoundedJoinSemilattice_674 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedJoinSemilattice_596
      (coe d_isBoundedLattice_666 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_280
d_isBoundedMeetSemilattice_676 ~v0 ~v1 ~v2 v3
  = du_isBoundedMeetSemilattice_676 v3
du_isBoundedMeetSemilattice_676 ::
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_280
du_isBoundedMeetSemilattice_676 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedMeetSemilattice_598
      (coe d_isBoundedLattice_666 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isEquivalence
d_isEquivalence_678 ::
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_678 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
               (coe d_isBoundedLattice_666 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isJoinSemilattice
d_isJoinSemilattice_680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_isJoinSemilattice_680 ~v0 ~v1 ~v2 v3
  = du_isJoinSemilattice_680 v3
du_isJoinSemilattice_680 ::
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_isJoinSemilattice_680 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isLattice
d_isLattice_682 ::
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_348
d_isLattice_682 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
      (coe d_isBoundedLattice_666 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isMeetSemilattice
d_isMeetSemilattice_684 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
d_isMeetSemilattice_684 ~v0 ~v1 ~v2 v3
  = du_isMeetSemilattice_684 v3
du_isMeetSemilattice_684 ::
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
du_isMeetSemilattice_684 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isPartialOrder
d_isPartialOrder_686 ::
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_686 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
         (coe d_isBoundedLattice_666 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isPreorder
d_isPreorder_688 ::
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_688 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
            (coe d_isBoundedLattice_666 (coe v0))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.maximum
d_maximum_690 :: T_BoundedLattice_628 -> AgdaAny -> AgdaAny
d_maximum_690 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_maximum_532
      (coe d_isBoundedLattice_666 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.minimum
d_minimum_692 :: T_BoundedLattice_628 -> AgdaAny -> AgdaAny
d_minimum_692 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_minimum_534
      (coe d_isBoundedLattice_666 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.refl
d_refl_694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 -> AgdaAny -> AgdaAny
d_refl_694 ~v0 ~v1 ~v2 v3 = du_refl_694 v3
du_refl_694 :: T_BoundedLattice_628 -> AgdaAny -> AgdaAny
du_refl_694 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_104
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.reflexive
d_reflexive_696 ::
  T_BoundedLattice_628 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_696 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
               (coe d_isBoundedLattice_666 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.supremum
d_supremum_698 ::
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_698 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_supremum_362
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
         (coe d_isBoundedLattice_666 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.trans
d_trans_700 ::
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_700 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
               (coe d_isBoundedLattice_666 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.x∧y≤x
d_x'8743'y'8804'x_702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_702 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'x_702 v3
du_x'8743'y'8804'x_702 ::
  T_BoundedLattice_628 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_702 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'x_200
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.x∧y≤y
d_x'8743'y'8804'y_704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_704 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'y_704 v3
du_x'8743'y'8804'y_704 ::
  T_BoundedLattice_628 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_704 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'y_212
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.x≤x∨y
d_x'8804'x'8744'y_706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_706 ~v0 ~v1 ~v2 v3 = du_x'8804'x'8744'y_706 v3
du_x'8804'x'8744'y_706 ::
  T_BoundedLattice_628 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_706 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.y≤x∨y
d_y'8804'x'8744'y_708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_708 ~v0 ~v1 ~v2 v3 = du_y'8804'x'8744'y_708 v3
du_y'8804'x'8744'y_708 ::
  T_BoundedLattice_628 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_708 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.∧-greatest
d_'8743''45'greatest_710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_710 ~v0 ~v1 ~v2 v3
  = du_'8743''45'greatest_710 v3
du_'8743''45'greatest_710 ::
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_710 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8743''45'greatest_226
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.∨-least
d_'8744''45'least_712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_712 ~v0 ~v1 ~v2 v3 = du_'8744''45'least_712 v3
du_'8744''45'least_712 ::
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_712 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_714 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_714 v3
du_'8764''45'resp'45''8776'_714 ::
  T_BoundedLattice_628 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_714 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_716 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_716 v3
du_'8764''45'resp'691''45''8776'_716 ::
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_716 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_718 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_718 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_718 v3
du_'8764''45'resp'737''45''8776'_718 ::
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_718 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_720 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_720 v3
du_'8818''45'resp'45''8776'_720 ::
  T_BoundedLattice_628 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_720 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_722 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_722 v3
du_'8818''45'resp'691''45''8776'_722 ::
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_722 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_724 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_724 v3
du_'8818''45'resp'737''45''8776'_724 ::
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_724 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_728 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_728 v3
du_isPartialEquivalence_728 ::
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_728 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.Eq.refl
d_refl_730 :: T_BoundedLattice_628 -> AgdaAny -> AgdaAny
d_refl_730 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                  (coe d_isBoundedLattice_666 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.Eq.reflexive
d_reflexive_732 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_732 ~v0 ~v1 ~v2 v3 = du_reflexive_732 v3
du_reflexive_732 ::
  T_BoundedLattice_628 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_732 v0
  = let v1 = d_isBoundedLattice_666 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.Eq.sym
d_sym_734 ::
  T_BoundedLattice_628 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_734 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                  (coe d_isBoundedLattice_666 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.Eq.trans
d_trans_736 ::
  T_BoundedLattice_628 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_736 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                  (coe d_isBoundedLattice_666 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice.boundedJoinSemilattice
d_boundedJoinSemilattice_738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 -> T_BoundedJoinSemilattice_104
d_boundedJoinSemilattice_738 ~v0 ~v1 ~v2 v3
  = du_boundedJoinSemilattice_738 v3
du_boundedJoinSemilattice_738 ::
  T_BoundedLattice_628 -> T_BoundedJoinSemilattice_104
du_boundedJoinSemilattice_738 v0
  = coe
      C_constructor_196 (d__'8744'__658 (coe v0)) (d_'8869'_664 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedJoinSemilattice_596
         (coe d_isBoundedLattice_666 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice.boundedMeetSemilattice
d_boundedMeetSemilattice_740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 -> T_BoundedMeetSemilattice_294
d_boundedMeetSemilattice_740 ~v0 ~v1 ~v2 v3
  = du_boundedMeetSemilattice_740 v3
du_boundedMeetSemilattice_740 ::
  T_BoundedLattice_628 -> T_BoundedMeetSemilattice_294
du_boundedMeetSemilattice_740 v0
  = coe
      C_constructor_386 (d__'8743'__660 (coe v0)) (d_'8868'_662 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedMeetSemilattice_598
         (coe d_isBoundedLattice_666 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice.lattice
d_lattice_742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 -> T_Lattice_394
d_lattice_742 ~v0 ~v1 ~v2 v3 = du_lattice_742 v3
du_lattice_742 :: T_BoundedLattice_628 -> T_Lattice_394
du_lattice_742 v0
  = coe
      C_constructor_498 (d__'8744'__658 (coe v0))
      (d__'8743'__660 (coe v0))
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
         (coe d_isBoundedLattice_666 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.joinSemilattice
d_joinSemilattice_746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 -> T_JoinSemilattice_14
d_joinSemilattice_746 ~v0 ~v1 ~v2 v3 = du_joinSemilattice_746 v3
du_joinSemilattice_746 ::
  T_BoundedLattice_628 -> T_JoinSemilattice_14
du_joinSemilattice_746 v0
  = coe du_joinSemilattice_488 (coe du_lattice_742 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.meetSemilattice
d_meetSemilattice_748 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 -> T_MeetSemilattice_204
d_meetSemilattice_748 ~v0 ~v1 ~v2 v3 = du_meetSemilattice_748 v3
du_meetSemilattice_748 ::
  T_BoundedLattice_628 -> T_MeetSemilattice_204
du_meetSemilattice_748 v0
  = coe du_meetSemilattice_490 (coe du_lattice_742 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.poset
d_poset_750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_750 ~v0 ~v1 ~v2 v3 = du_poset_750 v3
du_poset_750 ::
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_750 v0
  = let v1 = coe du_lattice_742 (coe v0) in
    coe (coe du_poset_90 (coe du_joinSemilattice_488 (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.preorder
d_preorder_752 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_preorder_752 ~v0 ~v1 ~v2 v3 = du_preorder_752 v3
du_preorder_752 ::
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_preorder_752 v0
  = let v1 = coe du_lattice_742 (coe v0) in
    coe
      (let v2 = coe du_joinSemilattice_488 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522
            (coe du_poset_90 (coe v2))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.setoid
d_setoid_754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_754 ~v0 ~v1 ~v2 v3 = du_setoid_754 v3
du_setoid_754 ::
  T_BoundedLattice_628 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_754 v0 = coe du_setoid_486 (coe du_lattice_742 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra
d_HeytingAlgebra_764 a0 a1 a2 = ()
data T_HeytingAlgebra_764
  = C_constructor_906 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny -> AgdaAny)
                      AgdaAny AgdaAny
                      MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsHeytingAlgebra_612
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra.Carrier
d_Carrier_790 :: T_HeytingAlgebra_764 -> ()
d_Carrier_790 = erased
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._≈_
d__'8776'__792 :: T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> ()
d__'8776'__792 = erased
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._≤_
d__'8804'__794 :: T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> ()
d__'8804'__794 = erased
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._∨_
d__'8744'__796 ::
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__796 v0
  = case coe v0 of
      C_constructor_906 v4 v5 v6 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._∧_
d__'8743'__798 ::
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__798 v0
  = case coe v0 of
      C_constructor_906 v4 v5 v6 v7 v8 v9 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._⇨_
d__'8680'__800 ::
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8680'__800 v0
  = case coe v0 of
      C_constructor_906 v4 v5 v6 v7 v8 v9 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra.⊤
d_'8868'_802 :: T_HeytingAlgebra_764 -> AgdaAny
d_'8868'_802 v0
  = case coe v0 of
      C_constructor_906 v4 v5 v6 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra.⊥
d_'8869'_804 :: T_HeytingAlgebra_764 -> AgdaAny
d_'8869'_804 v0
  = case coe v0 of
      C_constructor_906 v4 v5 v6 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra.isHeytingAlgebra
d_isHeytingAlgebra_806 ::
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsHeytingAlgebra_612
d_isHeytingAlgebra_806 v0
  = case coe v0 of
      C_constructor_906 v4 v5 v6 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra.boundedLattice
d_boundedLattice_808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> T_BoundedLattice_628
d_boundedLattice_808 ~v0 ~v1 ~v2 v3 = du_boundedLattice_808 v3
du_boundedLattice_808 ::
  T_HeytingAlgebra_764 -> T_BoundedLattice_628
du_boundedLattice_808 v0
  = coe
      C_constructor_756 (d__'8744'__796 (coe v0))
      (d__'8743'__798 (coe v0)) (d_'8868'_802 (coe v0))
      (d_'8869'_804 (coe v0))
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
         (coe d_isHeytingAlgebra_806 (coe v0)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.exponential
d_exponential_812 ::
  T_HeytingAlgebra_764 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exponential_812 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_exponential_630
      (coe d_isHeytingAlgebra_806 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.transpose-⇨
d_transpose'45''8680'_814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8680'_814 ~v0 ~v1 ~v2 v3
  = du_transpose'45''8680'_814 v3
du_transpose'45''8680'_814 ::
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8680'_814 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_transpose'45''8680'_638
      (coe d_isHeytingAlgebra_806 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.transpose-∧
d_transpose'45''8743'_816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8743'_816 ~v0 ~v1 ~v2 v3
  = du_transpose'45''8743'_816 v3
du_transpose'45''8743'_816 ::
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8743'_816 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_transpose'45''8743'_654
      (coe d_isHeytingAlgebra_806 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.antisym
d_antisym_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_820 ~v0 ~v1 ~v2 v3 = du_antisym_820 v3
du_antisym_820 ::
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_820 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
               (coe d_isHeytingAlgebra_806 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.boundedJoinSemilattice
d_boundedJoinSemilattice_822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> T_BoundedJoinSemilattice_104
d_boundedJoinSemilattice_822 ~v0 ~v1 ~v2 v3
  = du_boundedJoinSemilattice_822 v3
du_boundedJoinSemilattice_822 ::
  T_HeytingAlgebra_764 -> T_BoundedJoinSemilattice_104
du_boundedJoinSemilattice_822 v0
  = coe
      du_boundedJoinSemilattice_738 (coe du_boundedLattice_808 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.boundedMeetSemilattice
d_boundedMeetSemilattice_824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> T_BoundedMeetSemilattice_294
d_boundedMeetSemilattice_824 ~v0 ~v1 ~v2 v3
  = du_boundedMeetSemilattice_824 v3
du_boundedMeetSemilattice_824 ::
  T_HeytingAlgebra_764 -> T_BoundedMeetSemilattice_294
du_boundedMeetSemilattice_824 v0
  = coe
      du_boundedMeetSemilattice_740 (coe du_boundedLattice_808 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.infimum
d_infimum_826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_826 ~v0 ~v1 ~v2 v3 = du_infimum_826 v3
du_infimum_826 ::
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infimum_826 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_infimum_364
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
            (coe d_isHeytingAlgebra_806 (coe v0))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_118
d_isBoundedJoinSemilattice_828 ~v0 ~v1 ~v2 v3
  = du_isBoundedJoinSemilattice_828 v3
du_isBoundedJoinSemilattice_828 ::
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_118
du_isBoundedJoinSemilattice_828 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedJoinSemilattice_596
         (coe d_isBoundedLattice_666 (coe v1)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isBoundedLattice
d_isBoundedLattice_830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedLattice_514
d_isBoundedLattice_830 ~v0 ~v1 ~v2 v3 = du_isBoundedLattice_830 v3
du_isBoundedLattice_830 ::
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedLattice_514
du_isBoundedLattice_830 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
      (coe d_isHeytingAlgebra_806 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_280
d_isBoundedMeetSemilattice_832 ~v0 ~v1 ~v2 v3
  = du_isBoundedMeetSemilattice_832 v3
du_isBoundedMeetSemilattice_832 ::
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_280
du_isBoundedMeetSemilattice_832 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedMeetSemilattice_598
         (coe d_isBoundedLattice_666 (coe v1)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isEquivalence
d_isEquivalence_834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_834 ~v0 ~v1 ~v2 v3 = du_isEquivalence_834 v3
du_isEquivalence_834 ::
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_834 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
                  (coe d_isHeytingAlgebra_806 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isJoinSemilattice
d_isJoinSemilattice_836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_isJoinSemilattice_836 ~v0 ~v1 ~v2 v3
  = du_isJoinSemilattice_836 v3
du_isJoinSemilattice_836 ::
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_isJoinSemilattice_836 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isLattice
d_isLattice_838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_348
d_isLattice_838 ~v0 ~v1 ~v2 v3 = du_isLattice_838 v3
du_isLattice_838 ::
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_348
du_isLattice_838 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
         (coe d_isHeytingAlgebra_806 (coe v0)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isMeetSemilattice
d_isMeetSemilattice_840 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
d_isMeetSemilattice_840 ~v0 ~v1 ~v2 v3
  = du_isMeetSemilattice_840 v3
du_isMeetSemilattice_840 ::
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
du_isMeetSemilattice_840 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isPartialOrder
d_isPartialOrder_842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_842 ~v0 ~v1 ~v2 v3 = du_isPartialOrder_842 v3
du_isPartialOrder_842 ::
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_isPartialOrder_842 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
            (coe d_isHeytingAlgebra_806 (coe v0))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isPreorder
d_isPreorder_844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_844 ~v0 ~v1 ~v2 v3 = du_isPreorder_844 v3
du_isPreorder_844 ::
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_isPreorder_844 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
               (coe d_isHeytingAlgebra_806 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.joinSemilattice
d_joinSemilattice_846 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> T_JoinSemilattice_14
d_joinSemilattice_846 ~v0 ~v1 ~v2 v3 = du_joinSemilattice_846 v3
du_joinSemilattice_846 ::
  T_HeytingAlgebra_764 -> T_JoinSemilattice_14
du_joinSemilattice_846 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe (coe du_joinSemilattice_488 (coe du_lattice_742 (coe v1)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.lattice
d_lattice_848 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> T_Lattice_394
d_lattice_848 ~v0 ~v1 ~v2 v3 = du_lattice_848 v3
du_lattice_848 :: T_HeytingAlgebra_764 -> T_Lattice_394
du_lattice_848 v0
  = coe du_lattice_742 (coe du_boundedLattice_808 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.maximum
d_maximum_850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny
d_maximum_850 ~v0 ~v1 ~v2 v3 = du_maximum_850 v3
du_maximum_850 :: T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny
du_maximum_850 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_maximum_532
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
         (coe d_isHeytingAlgebra_806 (coe v0)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.meetSemilattice
d_meetSemilattice_852 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> T_MeetSemilattice_204
d_meetSemilattice_852 ~v0 ~v1 ~v2 v3 = du_meetSemilattice_852 v3
du_meetSemilattice_852 ::
  T_HeytingAlgebra_764 -> T_MeetSemilattice_204
du_meetSemilattice_852 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe (coe du_meetSemilattice_490 (coe du_lattice_742 (coe v1)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.minimum
d_minimum_854 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny
d_minimum_854 ~v0 ~v1 ~v2 v3 = du_minimum_854 v3
du_minimum_854 :: T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny
du_minimum_854 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_minimum_534
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
         (coe d_isHeytingAlgebra_806 (coe v0)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.poset
d_poset_856 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_856 ~v0 ~v1 ~v2 v3 = du_poset_856 v3
du_poset_856 ::
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_856 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = coe du_lattice_742 (coe v1) in
       coe (coe du_poset_90 (coe du_joinSemilattice_488 (coe v2))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.preorder
d_preorder_858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_preorder_858 ~v0 ~v1 ~v2 v3 = du_preorder_858 v3
du_preorder_858 ::
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_preorder_858 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = coe du_lattice_742 (coe v1) in
       coe
         (let v3 = coe du_joinSemilattice_488 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522
               (coe du_poset_90 (coe v3)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.refl
d_refl_860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny
d_refl_860 ~v0 ~v1 ~v2 v3 = du_refl_860 v3
du_refl_860 :: T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny
du_refl_860 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_refl_104
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.reflexive
d_reflexive_862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_862 ~v0 ~v1 ~v2 v3 = du_reflexive_862 v3
du_reflexive_862 ::
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_862 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
                  (coe d_isHeytingAlgebra_806 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.setoid
d_setoid_864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_864 ~v0 ~v1 ~v2 v3 = du_setoid_864 v3
du_setoid_864 ::
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_864 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe (coe du_setoid_486 (coe du_lattice_742 (coe v1)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.supremum
d_supremum_866 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_866 ~v0 ~v1 ~v2 v3 = du_supremum_866 v3
du_supremum_866 ::
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_supremum_866 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_supremum_362
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
            (coe d_isHeytingAlgebra_806 (coe v0))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.trans
d_trans_868 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_868 ~v0 ~v1 ~v2 v3 = du_trans_868 v3
du_trans_868 ::
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_868 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
                  (coe d_isHeytingAlgebra_806 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.x∧y≤x
d_x'8743'y'8804'x_870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_870 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'x_870 v3
du_x'8743'y'8804'x_870 ::
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_870 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'x_200
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.x∧y≤y
d_x'8743'y'8804'y_872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_872 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'y_872 v3
du_x'8743'y'8804'y_872 ::
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_872 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'y_212
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.x≤x∨y
d_x'8804'x'8744'y_874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_874 ~v0 ~v1 ~v2 v3 = du_x'8804'x'8744'y_874 v3
du_x'8804'x'8744'y_874 ::
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_874 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.y≤x∨y
d_y'8804'x'8744'y_876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_876 ~v0 ~v1 ~v2 v3 = du_y'8804'x'8744'y_876 v3
du_y'8804'x'8744'y_876 ::
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_876 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.∧-greatest
d_'8743''45'greatest_878 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_878 ~v0 ~v1 ~v2 v3
  = du_'8743''45'greatest_878 v3
du_'8743''45'greatest_878 ::
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_878 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8743''45'greatest_226
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.∨-least
d_'8744''45'least_880 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_880 ~v0 ~v1 ~v2 v3 = du_'8744''45'least_880 v3
du_'8744''45'least_880 ::
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_880 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.∼-resp-≈
d_'8764''45'resp'45''8776'_882 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_882 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_882 v3
du_'8764''45'resp'45''8776'_882 ::
  T_HeytingAlgebra_764 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_882 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_884 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_884 v3
du_'8764''45'resp'691''45''8776'_884 ::
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_884 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_886 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_886 v3
du_'8764''45'resp'737''45''8776'_886 ::
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_886 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.≲-resp-≈
d_'8818''45'resp'45''8776'_888 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_888 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_888 v3
du_'8818''45'resp'45''8776'_888 ::
  T_HeytingAlgebra_764 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_888 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_890 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_890 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_890 v3
du_'8818''45'resp'691''45''8776'_890 ::
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_890 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_892 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_892 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_892 v3
du_'8818''45'resp'737''45''8776'_892 ::
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_892 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.Eq.isPartialEquivalence
d_isPartialEquivalence_896 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_896 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_896 v3
du_isPartialEquivalence_896 ::
  T_HeytingAlgebra_764 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_896 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                       (coe v3) in
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
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.Eq.refl
d_refl_898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny
d_refl_898 ~v0 ~v1 ~v2 v3 = du_refl_898 v3
du_refl_898 :: T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny
du_refl_898 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
                     (coe d_isHeytingAlgebra_806 (coe v0)))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.Eq.reflexive
d_reflexive_900 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_900 ~v0 ~v1 ~v2 v3 = du_reflexive_900 v3
du_reflexive_900 ::
  T_HeytingAlgebra_764 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_900 v0
  = let v1 = coe du_boundedLattice_808 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_666 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                       (coe v3) in
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
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.Eq.sym
d_sym_902 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_902 ~v0 ~v1 ~v2 v3 = du_sym_902 v3
du_sym_902 ::
  T_HeytingAlgebra_764 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_902 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
                     (coe d_isHeytingAlgebra_806 (coe v0)))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.Eq.trans
d_trans_904 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_904 ~v0 ~v1 ~v2 v3 = du_trans_904 v3
du_trans_904 ::
  T_HeytingAlgebra_764 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_904 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
                     (coe d_isHeytingAlgebra_806 (coe v0)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra
d_BooleanAlgebra_914 a0 a1 a2 = ()
data T_BooleanAlgebra_914
  = C_constructor_1064 (AgdaAny -> AgdaAny -> AgdaAny)
                       (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny) AgdaAny
                       AgdaAny
                       MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBooleanAlgebra_746
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra.Carrier
d_Carrier_940 :: T_BooleanAlgebra_914 -> ()
d_Carrier_940 = erased
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._≈_
d__'8776'__942 :: T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> ()
d__'8776'__942 = erased
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._≤_
d__'8804'__944 :: T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> ()
d__'8804'__944 = erased
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._∨_
d__'8744'__946 ::
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__946 v0
  = case coe v0 of
      C_constructor_1064 v4 v5 v6 v7 v8 v9 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._∧_
d__'8743'__948 ::
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__948 v0
  = case coe v0 of
      C_constructor_1064 v4 v5 v6 v7 v8 v9 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra.¬_
d_'172'__950 :: T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny
d_'172'__950 v0
  = case coe v0 of
      C_constructor_1064 v4 v5 v6 v7 v8 v9 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra.⊤
d_'8868'_952 :: T_BooleanAlgebra_914 -> AgdaAny
d_'8868'_952 v0
  = case coe v0 of
      C_constructor_1064 v4 v5 v6 v7 v8 v9 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra.⊥
d_'8869'_954 :: T_BooleanAlgebra_914 -> AgdaAny
d_'8869'_954 v0
  = case coe v0 of
      C_constructor_1064 v4 v5 v6 v7 v8 v9 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra.isBooleanAlgebra
d_isBooleanAlgebra_956 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBooleanAlgebra_746
d_isBooleanAlgebra_956 v0
  = case coe v0 of
      C_constructor_1064 v4 v5 v6 v7 v8 v9 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra.heytingAlgebra
d_heytingAlgebra_962 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> T_HeytingAlgebra_764
d_heytingAlgebra_962 ~v0 ~v1 ~v2 v3 = du_heytingAlgebra_962 v3
du_heytingAlgebra_962 ::
  T_BooleanAlgebra_914 -> T_HeytingAlgebra_764
du_heytingAlgebra_962 v0
  = coe
      C_constructor_906 (d__'8744'__946 (coe v0))
      (d__'8743'__948 (coe v0))
      (\ v1 -> coe d__'8744'__946 v0 (coe d_'172'__950 v0 v1))
      (d_'8868'_952 (coe v0)) (d_'8869'_954 (coe v0))
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isHeytingAlgebra_772
         (coe d_isBooleanAlgebra_956 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._._⇨_
d__'8680'__966 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8680'__966 ~v0 ~v1 ~v2 v3 v4 = du__'8680'__966 v3 v4
du__'8680'__966 ::
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny
du__'8680'__966 v0 v1
  = coe d__'8744'__946 v0 (coe d_'172'__950 v0 v1)
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.antisym
d_antisym_968 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_968 ~v0 ~v1 ~v2 v3 = du_antisym_968 v3
du_antisym_968 ::
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_968 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_antisym_258
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
                  (coe d_isHeytingAlgebra_806 (coe v1))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.boundedJoinSemilattice
d_boundedJoinSemilattice_970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> T_BoundedJoinSemilattice_104
d_boundedJoinSemilattice_970 ~v0 ~v1 ~v2 v3
  = du_boundedJoinSemilattice_970 v3
du_boundedJoinSemilattice_970 ::
  T_BooleanAlgebra_914 -> T_BoundedJoinSemilattice_104
du_boundedJoinSemilattice_970 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         du_boundedJoinSemilattice_738 (coe du_boundedLattice_808 (coe v1)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.boundedLattice
d_boundedLattice_972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> T_BoundedLattice_628
d_boundedLattice_972 ~v0 ~v1 ~v2 v3 = du_boundedLattice_972 v3
du_boundedLattice_972 ::
  T_BooleanAlgebra_914 -> T_BoundedLattice_628
du_boundedLattice_972 v0
  = coe du_boundedLattice_808 (coe du_heytingAlgebra_962 (coe v0))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.boundedMeetSemilattice
d_boundedMeetSemilattice_974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> T_BoundedMeetSemilattice_294
d_boundedMeetSemilattice_974 ~v0 ~v1 ~v2 v3
  = du_boundedMeetSemilattice_974 v3
du_boundedMeetSemilattice_974 ::
  T_BooleanAlgebra_914 -> T_BoundedMeetSemilattice_294
du_boundedMeetSemilattice_974 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         du_boundedMeetSemilattice_740 (coe du_boundedLattice_808 (coe v1)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.exponential
d_exponential_976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exponential_976 ~v0 ~v1 ~v2 v3 = du_exponential_976 v3
du_exponential_976 ::
  T_BooleanAlgebra_914 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exponential_976 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_exponential_630
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isHeytingAlgebra_772
         (coe d_isBooleanAlgebra_956 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.infimum
d_infimum_978 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_978 ~v0 ~v1 ~v2 v3 = du_infimum_978 v3
du_infimum_978 ::
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infimum_978 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_infimum_364
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
               (coe d_isHeytingAlgebra_806 (coe v1)))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_118
d_isBoundedJoinSemilattice_980 ~v0 ~v1 ~v2 v3
  = du_isBoundedJoinSemilattice_980 v3
du_isBoundedJoinSemilattice_980 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_118
du_isBoundedJoinSemilattice_980 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedJoinSemilattice_596
            (coe d_isBoundedLattice_666 (coe v2))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isBoundedLattice
d_isBoundedLattice_982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedLattice_514
d_isBoundedLattice_982 ~v0 ~v1 ~v2 v3 = du_isBoundedLattice_982 v3
du_isBoundedLattice_982 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedLattice_514
du_isBoundedLattice_982 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
         (coe d_isHeytingAlgebra_806 (coe v1)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_280
d_isBoundedMeetSemilattice_984 ~v0 ~v1 ~v2 v3
  = du_isBoundedMeetSemilattice_984 v3
du_isBoundedMeetSemilattice_984 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_280
du_isBoundedMeetSemilattice_984 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedMeetSemilattice_598
            (coe d_isBoundedLattice_666 (coe v2))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isEquivalence
d_isEquivalence_986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_986 ~v0 ~v1 ~v2 v3 = du_isEquivalence_986 v3
du_isEquivalence_986 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_986 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
                     (coe d_isHeytingAlgebra_806 (coe v1)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isHeytingAlgebra
d_isHeytingAlgebra_988 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsHeytingAlgebra_612
d_isHeytingAlgebra_988 ~v0 ~v1 ~v2 v3 = du_isHeytingAlgebra_988 v3
du_isHeytingAlgebra_988 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsHeytingAlgebra_612
du_isHeytingAlgebra_988 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isHeytingAlgebra_772
      (coe d_isBooleanAlgebra_956 (coe v0))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isJoinSemilattice
d_isJoinSemilattice_990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_isJoinSemilattice_990 ~v0 ~v1 ~v2 v3
  = du_isJoinSemilattice_990 v3
du_isJoinSemilattice_990 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_isJoinSemilattice_990 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isLattice
d_isLattice_992 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_348
d_isLattice_992 ~v0 ~v1 ~v2 v3 = du_isLattice_992 v3
du_isLattice_992 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_348
du_isLattice_992 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
            (coe d_isHeytingAlgebra_806 (coe v1))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isMeetSemilattice
d_isMeetSemilattice_994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
d_isMeetSemilattice_994 ~v0 ~v1 ~v2 v3
  = du_isMeetSemilattice_994 v3
du_isMeetSemilattice_994 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
du_isMeetSemilattice_994 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isPartialOrder
d_isPartialOrder_996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_996 ~v0 ~v1 ~v2 v3 = du_isPartialOrder_996 v3
du_isPartialOrder_996 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_isPartialOrder_996 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
               (coe d_isHeytingAlgebra_806 (coe v1)))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isPreorder
d_isPreorder_998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_998 ~v0 ~v1 ~v2 v3 = du_isPreorder_998 v3
du_isPreorder_998 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_isPreorder_998 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
                  (coe d_isHeytingAlgebra_806 (coe v1))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.joinSemilattice
d_joinSemilattice_1000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> T_JoinSemilattice_14
d_joinSemilattice_1000 ~v0 ~v1 ~v2 v3 = du_joinSemilattice_1000 v3
du_joinSemilattice_1000 ::
  T_BooleanAlgebra_914 -> T_JoinSemilattice_14
du_joinSemilattice_1000 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe (coe du_joinSemilattice_488 (coe du_lattice_742 (coe v2))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.lattice
d_lattice_1002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> T_Lattice_394
d_lattice_1002 ~v0 ~v1 ~v2 v3 = du_lattice_1002 v3
du_lattice_1002 :: T_BooleanAlgebra_914 -> T_Lattice_394
du_lattice_1002 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe (coe du_lattice_742 (coe du_boundedLattice_808 (coe v1)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.maximum
d_maximum_1004 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny
d_maximum_1004 ~v0 ~v1 ~v2 v3 = du_maximum_1004 v3
du_maximum_1004 :: T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny
du_maximum_1004 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_maximum_532
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
            (coe d_isHeytingAlgebra_806 (coe v1))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.meetSemilattice
d_meetSemilattice_1006 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> T_MeetSemilattice_204
d_meetSemilattice_1006 ~v0 ~v1 ~v2 v3 = du_meetSemilattice_1006 v3
du_meetSemilattice_1006 ::
  T_BooleanAlgebra_914 -> T_MeetSemilattice_204
du_meetSemilattice_1006 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe (coe du_meetSemilattice_490 (coe du_lattice_742 (coe v2))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.minimum
d_minimum_1008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny
d_minimum_1008 ~v0 ~v1 ~v2 v3 = du_minimum_1008 v3
du_minimum_1008 :: T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny
du_minimum_1008 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_minimum_534
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
            (coe d_isHeytingAlgebra_806 (coe v1))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.poset
d_poset_1010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_1010 ~v0 ~v1 ~v2 v3 = du_poset_1010 v3
du_poset_1010 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_1010 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = coe du_lattice_742 (coe v2) in
          coe (coe du_poset_90 (coe du_joinSemilattice_488 (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.preorder
d_preorder_1012 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_preorder_1012 ~v0 ~v1 ~v2 v3 = du_preorder_1012 v3
du_preorder_1012 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_preorder_1012 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = coe du_lattice_742 (coe v2) in
          coe
            (let v4 = coe du_joinSemilattice_488 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.du_preorder_522
                  (coe du_poset_90 (coe v4))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.refl
d_refl_1014 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny
d_refl_1014 ~v0 ~v1 ~v2 v3 = du_refl_1014 v3
du_refl_1014 :: T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny
du_refl_1014 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_refl_104
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.reflexive
d_reflexive_1016 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_1016 ~v0 ~v1 ~v2 v3 = du_reflexive_1016 v3
du_reflexive_1016 ::
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_1016 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
                     (coe d_isHeytingAlgebra_806 (coe v1)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.setoid
d_setoid_1018 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_1018 ~v0 ~v1 ~v2 v3 = du_setoid_1018 v3
du_setoid_1018 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_1018 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe (coe du_setoid_486 (coe du_lattice_742 (coe v2))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.supremum
d_supremum_1020 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_1020 ~v0 ~v1 ~v2 v3 = du_supremum_1020 v3
du_supremum_1020 ::
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_supremum_1020 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_supremum_362
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
               (coe d_isHeytingAlgebra_806 (coe v1)))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.trans
d_trans_1022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1022 ~v0 ~v1 ~v2 v3 = du_trans_1022 v3
du_trans_1022 ::
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1022 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_90
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
                     (coe d_isHeytingAlgebra_806 (coe v1)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.transpose-⇨
d_transpose'45''8680'_1024 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8680'_1024 ~v0 ~v1 ~v2 v3
  = du_transpose'45''8680'_1024 v3
du_transpose'45''8680'_1024 ::
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8680'_1024 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_transpose'45''8680'_638
         (coe d_isHeytingAlgebra_806 (coe v1)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.transpose-∧
d_transpose'45''8743'_1026 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8743'_1026 ~v0 ~v1 ~v2 v3
  = du_transpose'45''8743'_1026 v3
du_transpose'45''8743'_1026 ::
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8743'_1026 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_transpose'45''8743'_654
         (coe d_isHeytingAlgebra_806 (coe v1)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.x∧y≤x
d_x'8743'y'8804'x_1028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_1028 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'x_1028 v3
du_x'8743'y'8804'x_1028 ::
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_1028 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'x_200
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.x∧y≤y
d_x'8743'y'8804'y_1030 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_1030 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'y_1030 v3
du_x'8743'y'8804'y_1030 ::
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_1030 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'y_212
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.x≤x∨y
d_x'8804'x'8744'y_1032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_1032 ~v0 ~v1 ~v2 v3 = du_x'8804'x'8744'y_1032 v3
du_x'8804'x'8744'y_1032 ::
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_1032 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.y≤x∨y
d_y'8804'x'8744'y_1034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_1034 ~v0 ~v1 ~v2 v3 = du_y'8804'x'8744'y_1034 v3
du_y'8804'x'8744'y_1034 ::
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_1034 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.∧-greatest
d_'8743''45'greatest_1036 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_1036 ~v0 ~v1 ~v2 v3
  = du_'8743''45'greatest_1036 v3
du_'8743''45'greatest_1036 ::
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_1036 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8743''45'greatest_226
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_368
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.∨-least
d_'8744''45'least_1038 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_1038 ~v0 ~v1 ~v2 v3 = du_'8744''45'least_1038 v3
du_'8744''45'least_1038 ::
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_1038 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_366
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.∼-resp-≈
d_'8764''45'resp'45''8776'_1040 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_1040 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_1040 v3
du_'8764''45'resp'45''8776'_1040 ::
  T_BooleanAlgebra_914 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_1040 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_1042 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_1042 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_1042 v3
du_'8764''45'resp'691''45''8776'_1042 ::
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_1042 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_122
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_1044 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_1044 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_1044 v3
du_'8764''45'resp'737''45''8776'_1044 ::
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_1044 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_120
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.≲-resp-≈
d_'8818''45'resp'45''8776'_1046 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_1046 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_1046 v3
du_'8818''45'resp'45''8776'_1046 ::
  T_BooleanAlgebra_914 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_1046 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_118
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_1048 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_1048 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_1048 v3
du_'8818''45'resp'691''45''8776'_1048 ::
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_1048 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_1050 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_1050 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_1050 v3
du_'8818''45'resp'737''45''8776'_1050 ::
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_1050 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                        (coe v5)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.Eq.isPartialEquivalence
d_isPartialEquivalence_1054 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1054 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1054 v3
du_isPartialEquivalence_1054 ::
  T_BooleanAlgebra_914 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1054 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                           (coe v6))))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.Eq.refl
d_refl_1056 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny
d_refl_1056 ~v0 ~v1 ~v2 v3 = du_refl_1056 v3
du_refl_1056 :: T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny
du_refl_1056 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                     (coe
                        MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
                        (coe d_isHeytingAlgebra_806 (coe v1))))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.Eq.reflexive
d_reflexive_1058 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1058 ~v0 ~v1 ~v2 v3 = du_reflexive_1058 v3
du_reflexive_1058 ::
  T_BooleanAlgebra_914 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1058 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_808 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_666 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
                             (coe v5) in
                   coe
                     (\ v7 v8 v9 ->
                        coe
                          MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                             (coe v6))
                          v7))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.Eq.sym
d_sym_1060 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1060 ~v0 ~v1 ~v2 v3 = du_sym_1060 v3
du_sym_1060 ::
  T_BooleanAlgebra_914 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1060 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                     (coe
                        MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
                        (coe d_isHeytingAlgebra_806 (coe v1))))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.Eq.trans
d_trans_1062 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1062 ~v0 ~v1 ~v2 v3 = du_trans_1062 v3
du_trans_1062 ::
  T_BooleanAlgebra_914 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1062 v0
  = let v1 = coe du_heytingAlgebra_962 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_360
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_530
                     (coe
                        MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_628
                        (coe d_isHeytingAlgebra_806 (coe v1))))))))
