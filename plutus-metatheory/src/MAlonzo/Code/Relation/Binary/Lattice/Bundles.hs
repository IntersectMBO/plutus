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

module MAlonzo.Code.Relation.Binary.Lattice.Bundles where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Lattice.Structures qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Lattice.Bundles.JoinSemilattice
d_JoinSemilattice_14 a0 a1 a2 = ()
data T_JoinSemilattice_14
  = C_JoinSemilattice'46'constructor_371 (AgdaAny ->
                                          AgdaAny -> AgdaAny)
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
      C_JoinSemilattice'46'constructor_371 v4 v5 -> coe v4
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.JoinSemilattice.isJoinSemilattice
d_isJoinSemilattice_40 ::
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_isJoinSemilattice_40 v0
  = case coe v0 of
      C_JoinSemilattice'46'constructor_371 v4 v5 -> coe v5
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.antisym
d_antisym_44 ::
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_44 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
         (coe d_isJoinSemilattice_40 (coe v0)))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.isEquivalence
d_isEquivalence_46 ::
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_46 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
            (coe d_isJoinSemilattice_40 (coe v0))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.isPartialOrder
d_isPartialOrder_48 ::
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_48 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
      (coe d_isJoinSemilattice_40 (coe v0))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.isPreorder
d_isPreorder_50 ::
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_50 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
            MAlonzo.Code.Relation.Binary.Structures.du_refl_98
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.reflexive
d_reflexive_54 ::
  T_JoinSemilattice_14 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_54 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
                = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.Eq.refl
d_refl_82 :: T_JoinSemilattice_14 -> AgdaAny -> AgdaAny
d_refl_82 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
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
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.Eq.sym
d_sym_86 ::
  T_JoinSemilattice_14 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_86 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
               (coe d_isJoinSemilattice_40 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.Eq.trans
d_trans_88 ::
  T_JoinSemilattice_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_88 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
               (coe d_isJoinSemilattice_40 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice.poset
d_poset_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_90 ~v0 ~v1 ~v2 v3 = du_poset_90 v3
du_poset_90 ::
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_90 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_6389
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
         (coe d_isJoinSemilattice_40 (coe v0)))
-- Relation.Binary.Lattice.Bundles.JoinSemilattice._.preorder
d_preorder_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_preorder_94 ~v0 ~v1 ~v2 v3 = du_preorder_94 v3
du_preorder_94 ::
  T_JoinSemilattice_14 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_preorder_94 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344
      (coe du_poset_90 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice
d_BoundedJoinSemilattice_102 a0 a1 a2 = ()
data T_BoundedJoinSemilattice_102
  = C_BoundedJoinSemilattice'46'constructor_2401 (AgdaAny ->
                                                  AgdaAny -> AgdaAny)
                                                 AgdaAny
                                                 MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_116
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice.Carrier
d_Carrier_122 :: T_BoundedJoinSemilattice_102 -> ()
d_Carrier_122 = erased
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._≈_
d__'8776'__124 ::
  T_BoundedJoinSemilattice_102 -> AgdaAny -> AgdaAny -> ()
d__'8776'__124 = erased
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._≤_
d__'8804'__126 ::
  T_BoundedJoinSemilattice_102 -> AgdaAny -> AgdaAny -> ()
d__'8804'__126 = erased
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._∨_
d__'8744'__128 ::
  T_BoundedJoinSemilattice_102 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__128 v0
  = case coe v0 of
      C_BoundedJoinSemilattice'46'constructor_2401 v4 v5 v6 -> coe v4
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice.⊥
d_'8869'_130 :: T_BoundedJoinSemilattice_102 -> AgdaAny
d_'8869'_130 v0
  = case coe v0 of
      C_BoundedJoinSemilattice'46'constructor_2401 v4 v5 v6 -> coe v5
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_132 ::
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_116
d_isBoundedJoinSemilattice_132 v0
  = case coe v0 of
      C_BoundedJoinSemilattice'46'constructor_2401 v4 v5 v6 -> coe v6
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.antisym
d_antisym_136 ::
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_136 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
            (coe d_isBoundedJoinSemilattice_132 (coe v0))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.isEquivalence
d_isEquivalence_138 ::
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_138 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
               (coe d_isBoundedJoinSemilattice_132 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.isJoinSemilattice
d_isJoinSemilattice_140 ::
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_isJoinSemilattice_140 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
      (coe d_isBoundedJoinSemilattice_132 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.isPartialOrder
d_isPartialOrder_142 ::
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_142 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
         (coe d_isBoundedJoinSemilattice_132 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.isPreorder
d_isPreorder_144 ::
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_144 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
            (coe d_isBoundedJoinSemilattice_132 (coe v0))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.minimum
d_minimum_146 :: T_BoundedJoinSemilattice_102 -> AgdaAny -> AgdaAny
d_minimum_146 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_minimum_128
      (coe d_isBoundedJoinSemilattice_132 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.refl
d_refl_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 -> AgdaAny -> AgdaAny
d_refl_148 ~v0 ~v1 ~v2 v3 = du_refl_148 v3
du_refl_148 :: T_BoundedJoinSemilattice_102 -> AgdaAny -> AgdaAny
du_refl_148 v0
  = let v1 = d_isBoundedJoinSemilattice_132 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_98
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.reflexive
d_reflexive_150 ::
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_150 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
               (coe d_isBoundedJoinSemilattice_132 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.supremum
d_supremum_152 ::
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_152 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_supremum_32
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
         (coe d_isBoundedJoinSemilattice_132 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.trans
d_trans_154 ::
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_154 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
               (coe d_isBoundedJoinSemilattice_132 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.x≤x∨y
d_x'8804'x'8744'y_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_156 ~v0 ~v1 ~v2 v3 = du_x'8804'x'8744'y_156 v3
du_x'8804'x'8744'y_156 ::
  T_BoundedJoinSemilattice_102 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_156 v0
  = let v1 = d_isBoundedJoinSemilattice_132 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.y≤x∨y
d_y'8804'x'8744'y_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_158 ~v0 ~v1 ~v2 v3 = du_y'8804'x'8744'y_158 v3
du_y'8804'x'8744'y_158 ::
  T_BoundedJoinSemilattice_102 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_158 v0
  = let v1 = d_isBoundedJoinSemilattice_132 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.∨-least
d_'8744''45'least_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_160 ~v0 ~v1 ~v2 v3 = du_'8744''45'least_160 v3
du_'8744''45'least_160 ::
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_160 v0
  = let v1 = d_isBoundedJoinSemilattice_132 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_162 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_162 v3
du_'8764''45'resp'45''8776'_162 ::
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_162 v0
  = let v1 = d_isBoundedJoinSemilattice_132 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_164 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_164 v3
du_'8764''45'resp'691''45''8776'_164 ::
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_164 v0
  = let v1 = d_isBoundedJoinSemilattice_132 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_166 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_166 v3
du_'8764''45'resp'737''45''8776'_166 ::
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_166 v0
  = let v1 = d_isBoundedJoinSemilattice_132 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_168 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_168 v3
du_'8818''45'resp'45''8776'_168 ::
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_168 v0
  = let v1 = d_isBoundedJoinSemilattice_132 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_170 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_170 v3
du_'8818''45'resp'691''45''8776'_170 ::
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_170 v0
  = let v1 = d_isBoundedJoinSemilattice_132 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_172 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_172 v3
du_'8818''45'resp'737''45''8776'_172 ::
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_172 v0
  = let v1 = d_isBoundedJoinSemilattice_132 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_176 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_176 v3
du_isPartialEquivalence_176 ::
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_176 v0
  = let v1 = d_isBoundedJoinSemilattice_132 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.Eq.refl
d_refl_178 :: T_BoundedJoinSemilattice_102 -> AgdaAny -> AgdaAny
d_refl_178 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
                  (coe d_isBoundedJoinSemilattice_132 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.Eq.reflexive
d_reflexive_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_180 ~v0 ~v1 ~v2 v3 = du_reflexive_180 v3
du_reflexive_180 ::
  T_BoundedJoinSemilattice_102 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_180 v0
  = let v1 = d_isBoundedJoinSemilattice_132 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.Eq.sym
d_sym_182 ::
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_182 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
                  (coe d_isBoundedJoinSemilattice_132 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.Eq.trans
d_trans_184 ::
  T_BoundedJoinSemilattice_102 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_184 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_30
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
                  (coe d_isBoundedJoinSemilattice_132 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice.joinSemilattice
d_joinSemilattice_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 -> T_JoinSemilattice_14
d_joinSemilattice_186 ~v0 ~v1 ~v2 v3 = du_joinSemilattice_186 v3
du_joinSemilattice_186 ::
  T_BoundedJoinSemilattice_102 -> T_JoinSemilattice_14
du_joinSemilattice_186 v0
  = coe
      C_JoinSemilattice'46'constructor_371 (d__'8744'__128 (coe v0))
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isJoinSemilattice_126
         (coe d_isBoundedJoinSemilattice_132 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.poset
d_poset_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_190 ~v0 ~v1 ~v2 v3 = du_poset_190 v3
du_poset_190 ::
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_190 v0
  = coe du_poset_90 (coe du_joinSemilattice_186 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedJoinSemilattice._.preorder
d_preorder_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_preorder_192 ~v0 ~v1 ~v2 v3 = du_preorder_192 v3
du_preorder_192 ::
  T_BoundedJoinSemilattice_102 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_preorder_192 v0
  = let v1 = coe du_joinSemilattice_186 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344
         (coe du_poset_90 (coe v1)))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice
d_MeetSemilattice_200 a0 a1 a2 = ()
data T_MeetSemilattice_200
  = C_MeetSemilattice'46'constructor_4629 (AgdaAny ->
                                           AgdaAny -> AgdaAny)
                                          MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
-- Relation.Binary.Lattice.Bundles.MeetSemilattice.Carrier
d_Carrier_218 :: T_MeetSemilattice_200 -> ()
d_Carrier_218 = erased
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._≈_
d__'8776'__220 :: T_MeetSemilattice_200 -> AgdaAny -> AgdaAny -> ()
d__'8776'__220 = erased
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._≤_
d__'8804'__222 :: T_MeetSemilattice_200 -> AgdaAny -> AgdaAny -> ()
d__'8804'__222 = erased
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._∧_
d__'8743'__224 ::
  T_MeetSemilattice_200 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__224 v0
  = case coe v0 of
      C_MeetSemilattice'46'constructor_4629 v4 v5 -> coe v4
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.MeetSemilattice.isMeetSemilattice
d_isMeetSemilattice_226 ::
  T_MeetSemilattice_200 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
d_isMeetSemilattice_226 v0
  = case coe v0 of
      C_MeetSemilattice'46'constructor_4629 v4 v5 -> coe v5
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.antisym
d_antisym_230 ::
  T_MeetSemilattice_200 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_230 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
         (coe d_isMeetSemilattice_226 (coe v0)))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.infimum
d_infimum_232 ::
  T_MeetSemilattice_200 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_232 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_infimum_190
      (coe d_isMeetSemilattice_226 (coe v0))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.isEquivalence
d_isEquivalence_234 ::
  T_MeetSemilattice_200 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_234 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
            (coe d_isMeetSemilattice_226 (coe v0))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.isPartialOrder
d_isPartialOrder_236 ::
  T_MeetSemilattice_200 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_236 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
      (coe d_isMeetSemilattice_226 (coe v0))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.isPreorder
d_isPreorder_238 ::
  T_MeetSemilattice_200 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_238 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
         (coe d_isMeetSemilattice_226 (coe v0)))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.refl
d_refl_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_200 -> AgdaAny -> AgdaAny
d_refl_240 ~v0 ~v1 ~v2 v3 = du_refl_240 v3
du_refl_240 :: T_MeetSemilattice_200 -> AgdaAny -> AgdaAny
du_refl_240 v0
  = let v1 = d_isMeetSemilattice_226 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_98
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.reflexive
d_reflexive_242 ::
  T_MeetSemilattice_200 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_242 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
            (coe d_isMeetSemilattice_226 (coe v0))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.trans
d_trans_244 ::
  T_MeetSemilattice_200 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_244 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
            (coe d_isMeetSemilattice_226 (coe v0))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.x∧y≤x
d_x'8743'y'8804'x_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_200 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_246 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'x_246 v3
du_x'8743'y'8804'x_246 ::
  T_MeetSemilattice_200 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_246 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'x_196
      (coe d_isMeetSemilattice_226 (coe v0))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.x∧y≤y
d_x'8743'y'8804'y_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_200 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_248 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'y_248 v3
du_x'8743'y'8804'y_248 ::
  T_MeetSemilattice_200 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_248 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'y_208
      (coe d_isMeetSemilattice_226 (coe v0))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.∧-greatest
d_'8743''45'greatest_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_200 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_250 ~v0 ~v1 ~v2 v3
  = du_'8743''45'greatest_250 v3
du_'8743''45'greatest_250 ::
  T_MeetSemilattice_200 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_250 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8743''45'greatest_222
      (coe d_isMeetSemilattice_226 (coe v0))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_200 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_252 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_252 v3
du_'8764''45'resp'45''8776'_252 ::
  T_MeetSemilattice_200 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_252 v0
  = let v1 = d_isMeetSemilattice_226 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_200 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_254 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_254 v3
du_'8764''45'resp'691''45''8776'_254 ::
  T_MeetSemilattice_200 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_254 v0
  = let v1 = d_isMeetSemilattice_226 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_200 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_256 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_256 v3
du_'8764''45'resp'737''45''8776'_256 ::
  T_MeetSemilattice_200 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_256 v0
  = let v1 = d_isMeetSemilattice_226 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_200 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_258 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_258 v3
du_'8818''45'resp'45''8776'_258 ::
  T_MeetSemilattice_200 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_258 v0
  = let v1 = d_isMeetSemilattice_226 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_200 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_260 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_260 v3
du_'8818''45'resp'691''45''8776'_260 ::
  T_MeetSemilattice_200 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_260 v0
  = let v1 = d_isMeetSemilattice_226 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_200 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_262 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_262 v3
du_'8818''45'resp'737''45''8776'_262 ::
  T_MeetSemilattice_200 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_262 v0
  = let v1 = d_isMeetSemilattice_226 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_200 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_266 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_266 v3
du_isPartialEquivalence_266 ::
  T_MeetSemilattice_200 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_266 v0
  = let v1 = d_isMeetSemilattice_226 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                 (coe v1) in
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
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.Eq.refl
d_refl_268 :: T_MeetSemilattice_200 -> AgdaAny -> AgdaAny
d_refl_268 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
               (coe d_isMeetSemilattice_226 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.Eq.reflexive
d_reflexive_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_200 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_270 ~v0 ~v1 ~v2 v3 = du_reflexive_270 v3
du_reflexive_270 ::
  T_MeetSemilattice_200 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_270 v0
  = let v1 = d_isMeetSemilattice_226 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                 (coe v1) in
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
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.Eq.sym
d_sym_272 ::
  T_MeetSemilattice_200 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_272 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
               (coe d_isMeetSemilattice_226 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.Eq.trans
d_trans_274 ::
  T_MeetSemilattice_200 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_274 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
               (coe d_isMeetSemilattice_226 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice.poset
d_poset_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_200 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_276 ~v0 ~v1 ~v2 v3 = du_poset_276 v3
du_poset_276 ::
  T_MeetSemilattice_200 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_276 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_6389
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
         (coe d_isMeetSemilattice_226 (coe v0)))
-- Relation.Binary.Lattice.Bundles.MeetSemilattice._.preorder
d_preorder_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_200 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_preorder_280 ~v0 ~v1 ~v2 v3 = du_preorder_280 v3
du_preorder_280 ::
  T_MeetSemilattice_200 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_preorder_280 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344
      (coe du_poset_276 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice
d_BoundedMeetSemilattice_288 a0 a1 a2 = ()
data T_BoundedMeetSemilattice_288
  = C_BoundedMeetSemilattice'46'constructor_6659 (AgdaAny ->
                                                  AgdaAny -> AgdaAny)
                                                 AgdaAny
                                                 MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_274
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice.Carrier
d_Carrier_308 :: T_BoundedMeetSemilattice_288 -> ()
d_Carrier_308 = erased
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._≈_
d__'8776'__310 ::
  T_BoundedMeetSemilattice_288 -> AgdaAny -> AgdaAny -> ()
d__'8776'__310 = erased
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._≤_
d__'8804'__312 ::
  T_BoundedMeetSemilattice_288 -> AgdaAny -> AgdaAny -> ()
d__'8804'__312 = erased
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._∧_
d__'8743'__314 ::
  T_BoundedMeetSemilattice_288 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__314 v0
  = case coe v0 of
      C_BoundedMeetSemilattice'46'constructor_6659 v4 v5 v6 -> coe v4
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice.⊤
d_'8868'_316 :: T_BoundedMeetSemilattice_288 -> AgdaAny
d_'8868'_316 v0
  = case coe v0 of
      C_BoundedMeetSemilattice'46'constructor_6659 v4 v5 v6 -> coe v5
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_318 ::
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_274
d_isBoundedMeetSemilattice_318 v0
  = case coe v0 of
      C_BoundedMeetSemilattice'46'constructor_6659 v4 v5 v6 -> coe v6
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.antisym
d_antisym_322 ::
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_322 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
            (coe d_isBoundedMeetSemilattice_318 (coe v0))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.infimum
d_infimum_324 ::
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_324 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_infimum_190
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
         (coe d_isBoundedMeetSemilattice_318 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.isEquivalence
d_isEquivalence_326 ::
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_326 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
               (coe d_isBoundedMeetSemilattice_318 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.isMeetSemilattice
d_isMeetSemilattice_328 ::
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
d_isMeetSemilattice_328 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
      (coe d_isBoundedMeetSemilattice_318 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.isPartialOrder
d_isPartialOrder_330 ::
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_330 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
         (coe d_isBoundedMeetSemilattice_318 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.isPreorder
d_isPreorder_332 ::
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_332 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
            (coe d_isBoundedMeetSemilattice_318 (coe v0))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.maximum
d_maximum_334 :: T_BoundedMeetSemilattice_288 -> AgdaAny -> AgdaAny
d_maximum_334 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_maximum_286
      (coe d_isBoundedMeetSemilattice_318 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.refl
d_refl_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 -> AgdaAny -> AgdaAny
d_refl_336 ~v0 ~v1 ~v2 v3 = du_refl_336 v3
du_refl_336 :: T_BoundedMeetSemilattice_288 -> AgdaAny -> AgdaAny
du_refl_336 v0
  = let v1 = d_isBoundedMeetSemilattice_318 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_98
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.reflexive
d_reflexive_338 ::
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_338 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
               (coe d_isBoundedMeetSemilattice_318 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.trans
d_trans_340 ::
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_340 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
               (coe d_isBoundedMeetSemilattice_318 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.x∧y≤x
d_x'8743'y'8804'x_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_342 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'x_342 v3
du_x'8743'y'8804'x_342 ::
  T_BoundedMeetSemilattice_288 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_342 v0
  = let v1 = d_isBoundedMeetSemilattice_318 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'x_196
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.x∧y≤y
d_x'8743'y'8804'y_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_344 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'y_344 v3
du_x'8743'y'8804'y_344 ::
  T_BoundedMeetSemilattice_288 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_344 v0
  = let v1 = d_isBoundedMeetSemilattice_318 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'y_208
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.∧-greatest
d_'8743''45'greatest_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_346 ~v0 ~v1 ~v2 v3
  = du_'8743''45'greatest_346 v3
du_'8743''45'greatest_346 ::
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_346 v0
  = let v1 = d_isBoundedMeetSemilattice_318 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8743''45'greatest_222
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_348 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_348 v3
du_'8764''45'resp'45''8776'_348 ::
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_348 v0
  = let v1 = d_isBoundedMeetSemilattice_318 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_350 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_350 v3
du_'8764''45'resp'691''45''8776'_350 ::
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_350 v0
  = let v1 = d_isBoundedMeetSemilattice_318 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_352 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_352 v3
du_'8764''45'resp'737''45''8776'_352 ::
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_352 v0
  = let v1 = d_isBoundedMeetSemilattice_318 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_354 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_354 v3
du_'8818''45'resp'45''8776'_354 ::
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_354 v0
  = let v1 = d_isBoundedMeetSemilattice_318 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_356 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_356 v3
du_'8818''45'resp'691''45''8776'_356 ::
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_356 v0
  = let v1 = d_isBoundedMeetSemilattice_318 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_358 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_358 v3
du_'8818''45'resp'737''45''8776'_358 ::
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_358 v0
  = let v1 = d_isBoundedMeetSemilattice_318 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_362 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_362 v3
du_isPartialEquivalence_362 ::
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_362 v0
  = let v1 = d_isBoundedMeetSemilattice_318 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.Eq.refl
d_refl_364 :: T_BoundedMeetSemilattice_288 -> AgdaAny -> AgdaAny
d_refl_364 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
                  (coe d_isBoundedMeetSemilattice_318 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.Eq.reflexive
d_reflexive_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_366 ~v0 ~v1 ~v2 v3 = du_reflexive_366 v3
du_reflexive_366 ::
  T_BoundedMeetSemilattice_288 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_366 v0
  = let v1 = d_isBoundedMeetSemilattice_318 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.Eq.sym
d_sym_368 ::
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_368 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
                  (coe d_isBoundedMeetSemilattice_318 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.Eq.trans
d_trans_370 ::
  T_BoundedMeetSemilattice_288 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_370 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_188
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
                  (coe d_isBoundedMeetSemilattice_318 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice.meetSemilattice
d_meetSemilattice_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 -> T_MeetSemilattice_200
d_meetSemilattice_372 ~v0 ~v1 ~v2 v3 = du_meetSemilattice_372 v3
du_meetSemilattice_372 ::
  T_BoundedMeetSemilattice_288 -> T_MeetSemilattice_200
du_meetSemilattice_372 v0
  = coe
      C_MeetSemilattice'46'constructor_4629 (d__'8743'__314 (coe v0))
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isMeetSemilattice_284
         (coe d_isBoundedMeetSemilattice_318 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.poset
d_poset_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_376 ~v0 ~v1 ~v2 v3 = du_poset_376 v3
du_poset_376 ::
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_376 v0
  = coe du_poset_276 (coe du_meetSemilattice_372 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedMeetSemilattice._.preorder
d_preorder_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_preorder_378 ~v0 ~v1 ~v2 v3 = du_preorder_378 v3
du_preorder_378 ::
  T_BoundedMeetSemilattice_288 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_preorder_378 v0
  = let v1 = coe du_meetSemilattice_372 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344
         (coe du_poset_276 (coe v1)))
-- Relation.Binary.Lattice.Bundles.Lattice
d_Lattice_386 a0 a1 a2 = ()
data T_Lattice_386
  = C_Lattice'46'constructor_8977 (AgdaAny -> AgdaAny -> AgdaAny)
                                  (AgdaAny -> AgdaAny -> AgdaAny)
                                  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
-- Relation.Binary.Lattice.Bundles.Lattice.Carrier
d_Carrier_406 :: T_Lattice_386 -> ()
d_Carrier_406 = erased
-- Relation.Binary.Lattice.Bundles.Lattice._≈_
d__'8776'__408 :: T_Lattice_386 -> AgdaAny -> AgdaAny -> ()
d__'8776'__408 = erased
-- Relation.Binary.Lattice.Bundles.Lattice._≤_
d__'8804'__410 :: T_Lattice_386 -> AgdaAny -> AgdaAny -> ()
d__'8804'__410 = erased
-- Relation.Binary.Lattice.Bundles.Lattice._∨_
d__'8744'__412 :: T_Lattice_386 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__412 v0
  = case coe v0 of
      C_Lattice'46'constructor_8977 v4 v5 v6 -> coe v4
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.Lattice._∧_
d__'8743'__414 :: T_Lattice_386 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__414 v0
  = case coe v0 of
      C_Lattice'46'constructor_8977 v4 v5 v6 -> coe v5
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.Lattice.isLattice
d_isLattice_416 ::
  T_Lattice_386 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
d_isLattice_416 v0
  = case coe v0 of
      C_Lattice'46'constructor_8977 v4 v5 v6 -> coe v6
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.Lattice._.antisym
d_antisym_420 ::
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_420 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
         (coe d_isLattice_416 (coe v0)))
-- Relation.Binary.Lattice.Bundles.Lattice._.infimum
d_infimum_422 ::
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_422 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_infimum_356
      (coe d_isLattice_416 (coe v0))
-- Relation.Binary.Lattice.Bundles.Lattice._.isEquivalence
d_isEquivalence_424 ::
  T_Lattice_386 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_424 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
            (coe d_isLattice_416 (coe v0))))
-- Relation.Binary.Lattice.Bundles.Lattice._.isJoinSemilattice
d_isJoinSemilattice_426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_isJoinSemilattice_426 ~v0 ~v1 ~v2 v3
  = du_isJoinSemilattice_426 v3
du_isJoinSemilattice_426 ::
  T_Lattice_386 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_isJoinSemilattice_426 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
      (coe d_isLattice_416 (coe v0))
-- Relation.Binary.Lattice.Bundles.Lattice._.isMeetSemilattice
d_isMeetSemilattice_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
d_isMeetSemilattice_428 ~v0 ~v1 ~v2 v3
  = du_isMeetSemilattice_428 v3
du_isMeetSemilattice_428 ::
  T_Lattice_386 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
du_isMeetSemilattice_428 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
      (coe d_isLattice_416 (coe v0))
-- Relation.Binary.Lattice.Bundles.Lattice._.isPartialOrder
d_isPartialOrder_430 ::
  T_Lattice_386 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_430 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
      (coe d_isLattice_416 (coe v0))
-- Relation.Binary.Lattice.Bundles.Lattice._.isPreorder
d_isPreorder_432 ::
  T_Lattice_386 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_432 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
         (coe d_isLattice_416 (coe v0)))
-- Relation.Binary.Lattice.Bundles.Lattice._.refl
d_refl_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 -> AgdaAny -> AgdaAny
d_refl_434 ~v0 ~v1 ~v2 v3 = du_refl_434 v3
du_refl_434 :: T_Lattice_386 -> AgdaAny -> AgdaAny
du_refl_434 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_refl_98
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.Lattice._.reflexive
d_reflexive_436 ::
  T_Lattice_386 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_436 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
            (coe d_isLattice_416 (coe v0))))
-- Relation.Binary.Lattice.Bundles.Lattice._.supremum
d_supremum_438 ::
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_438 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_supremum_354
      (coe d_isLattice_416 (coe v0))
-- Relation.Binary.Lattice.Bundles.Lattice._.trans
d_trans_440 ::
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_440 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
            (coe d_isLattice_416 (coe v0))))
-- Relation.Binary.Lattice.Bundles.Lattice._.x∧y≤x
d_x'8743'y'8804'x_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_442 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'x_442 v3
du_x'8743'y'8804'x_442 ::
  T_Lattice_386 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_442 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'x_196
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.Lattice._.x∧y≤y
d_x'8743'y'8804'y_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_444 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'y_444 v3
du_x'8743'y'8804'y_444 ::
  T_Lattice_386 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_444 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'y_208
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.Lattice._.x≤x∨y
d_x'8804'x'8744'y_446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_446 ~v0 ~v1 ~v2 v3 = du_x'8804'x'8744'y_446 v3
du_x'8804'x'8744'y_446 ::
  T_Lattice_386 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_446 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.Lattice._.y≤x∨y
d_y'8804'x'8744'y_448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_448 ~v0 ~v1 ~v2 v3 = du_y'8804'x'8744'y_448 v3
du_y'8804'x'8744'y_448 ::
  T_Lattice_386 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_448 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.Lattice._.∧-greatest
d_'8743''45'greatest_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_450 ~v0 ~v1 ~v2 v3
  = du_'8743''45'greatest_450 v3
du_'8743''45'greatest_450 ::
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_450 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8743''45'greatest_222
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.Lattice._.∨-least
d_'8744''45'least_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_452 ~v0 ~v1 ~v2 v3 = du_'8744''45'least_452 v3
du_'8744''45'least_452 ::
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_452 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.Lattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_454 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_454 v3
du_'8764''45'resp'45''8776'_454 ::
  T_Lattice_386 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_454 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.Lattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_456 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_456 v3
du_'8764''45'resp'691''45''8776'_456 ::
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_456 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.Lattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_458 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_458 v3
du_'8764''45'resp'737''45''8776'_458 ::
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_458 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.Lattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_460 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_460 v3
du_'8818''45'resp'45''8776'_460 ::
  T_Lattice_386 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_460 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.Lattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_462 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_462 v3
du_'8818''45'resp'691''45''8776'_462 ::
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_462 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.Lattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_464 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_464 v3
du_'8818''45'resp'737''45''8776'_464 ::
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_464 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.Lattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_468 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_468 v3
du_isPartialEquivalence_468 ::
  T_Lattice_386 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_468 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                 (coe v1) in
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
-- Relation.Binary.Lattice.Bundles.Lattice._.Eq.refl
d_refl_470 :: T_Lattice_386 -> AgdaAny -> AgdaAny
d_refl_470 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe d_isLattice_416 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.Lattice._.Eq.reflexive
d_reflexive_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_472 ~v0 ~v1 ~v2 v3 = du_reflexive_472 v3
du_reflexive_472 ::
  T_Lattice_386 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_472 v0
  = let v1 = d_isLattice_416 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                 (coe v1) in
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
-- Relation.Binary.Lattice.Bundles.Lattice._.Eq.sym
d_sym_474 ::
  T_Lattice_386 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_474 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe d_isLattice_416 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.Lattice._.Eq.trans
d_trans_476 ::
  T_Lattice_386 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_476 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe d_isLattice_416 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.Lattice.setoid
d_setoid_478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_478 ~v0 ~v1 ~v2 v3 = du_setoid_478 v3
du_setoid_478 ::
  T_Lattice_386 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_478 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_733
      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe d_isLattice_416 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.Lattice.joinSemilattice
d_joinSemilattice_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 -> T_JoinSemilattice_14
d_joinSemilattice_480 ~v0 ~v1 ~v2 v3 = du_joinSemilattice_480 v3
du_joinSemilattice_480 :: T_Lattice_386 -> T_JoinSemilattice_14
du_joinSemilattice_480 v0
  = coe
      C_JoinSemilattice'46'constructor_371 (d__'8744'__412 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
         (coe d_isLattice_416 (coe v0)))
-- Relation.Binary.Lattice.Bundles.Lattice.meetSemilattice
d_meetSemilattice_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 -> T_MeetSemilattice_200
d_meetSemilattice_482 ~v0 ~v1 ~v2 v3 = du_meetSemilattice_482 v3
du_meetSemilattice_482 :: T_Lattice_386 -> T_MeetSemilattice_200
du_meetSemilattice_482 v0
  = coe
      C_MeetSemilattice'46'constructor_4629 (d__'8743'__414 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
         (coe d_isLattice_416 (coe v0)))
-- Relation.Binary.Lattice.Bundles.Lattice._.poset
d_poset_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 -> MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_486 ~v0 ~v1 ~v2 v3 = du_poset_486 v3
du_poset_486 ::
  T_Lattice_386 -> MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_486 v0
  = coe du_poset_90 (coe du_joinSemilattice_480 (coe v0))
-- Relation.Binary.Lattice.Bundles.Lattice._.preorder
d_preorder_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_386 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_preorder_488 ~v0 ~v1 ~v2 v3 = du_preorder_488 v3
du_preorder_488 ::
  T_Lattice_386 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_preorder_488 v0
  = let v1 = coe du_joinSemilattice_480 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344
         (coe du_poset_90 (coe v1)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice
d_DistributiveLattice_496 a0 a1 a2 = ()
data T_DistributiveLattice_496
  = C_DistributiveLattice'46'constructor_11867 (AgdaAny ->
                                                AgdaAny -> AgdaAny)
                                               (AgdaAny -> AgdaAny -> AgdaAny)
                                               MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsDistributiveLattice_420
-- Relation.Binary.Lattice.Bundles.DistributiveLattice.Carrier
d_Carrier_516 :: T_DistributiveLattice_496 -> ()
d_Carrier_516 = erased
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._≈_
d__'8776'__518 ::
  T_DistributiveLattice_496 -> AgdaAny -> AgdaAny -> ()
d__'8776'__518 = erased
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._≤_
d__'8804'__520 ::
  T_DistributiveLattice_496 -> AgdaAny -> AgdaAny -> ()
d__'8804'__520 = erased
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._∨_
d__'8744'__522 ::
  T_DistributiveLattice_496 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__522 v0
  = case coe v0 of
      C_DistributiveLattice'46'constructor_11867 v4 v5 v6 -> coe v4
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._∧_
d__'8743'__524 ::
  T_DistributiveLattice_496 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__524 v0
  = case coe v0 of
      C_DistributiveLattice'46'constructor_11867 v4 v5 v6 -> coe v5
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.DistributiveLattice.isDistributiveLattice
d_isDistributiveLattice_526 ::
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsDistributiveLattice_420
d_isDistributiveLattice_526 v0
  = case coe v0 of
      C_DistributiveLattice'46'constructor_11867 v4 v5 v6 -> coe v6
      _                                                   -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_530 ::
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8744'_530 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_'8743''45'distrib'737''45''8744'_432
      (coe d_isDistributiveLattice_526 (coe v0))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice.lattice
d_lattice_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 -> T_Lattice_386
d_lattice_536 ~v0 ~v1 ~v2 v3 = du_lattice_536 v3
du_lattice_536 :: T_DistributiveLattice_496 -> T_Lattice_386
du_lattice_536 v0
  = coe
      C_Lattice'46'constructor_8977 (d__'8744'__522 (coe v0))
      (d__'8743'__524 (coe v0))
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_430
         (coe d_isDistributiveLattice_526 (coe v0)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.antisym
d_antisym_540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_540 ~v0 ~v1 ~v2 v3 = du_antisym_540 v3
du_antisym_540 ::
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_540 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_430
            (coe d_isDistributiveLattice_526 (coe v0))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.infimum
d_infimum_542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_542 ~v0 ~v1 ~v2 v3 = du_infimum_542 v3
du_infimum_542 ::
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infimum_542 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_infimum_356
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_430
         (coe d_isDistributiveLattice_526 (coe v0)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.isEquivalence
d_isEquivalence_544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_544 ~v0 ~v1 ~v2 v3 = du_isEquivalence_544 v3
du_isEquivalence_544 ::
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_544 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_430
               (coe d_isDistributiveLattice_526 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.isJoinSemilattice
d_isJoinSemilattice_546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_isJoinSemilattice_546 ~v0 ~v1 ~v2 v3
  = du_isJoinSemilattice_546 v3
du_isJoinSemilattice_546 ::
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_isJoinSemilattice_546 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
         (coe d_isLattice_416 (coe v1)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.isLattice
d_isLattice_548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
d_isLattice_548 ~v0 ~v1 ~v2 v3 = du_isLattice_548 v3
du_isLattice_548 ::
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
du_isLattice_548 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_430
      (coe d_isDistributiveLattice_526 (coe v0))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.isMeetSemilattice
d_isMeetSemilattice_550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
d_isMeetSemilattice_550 ~v0 ~v1 ~v2 v3
  = du_isMeetSemilattice_550 v3
du_isMeetSemilattice_550 ::
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
du_isMeetSemilattice_550 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
         (coe d_isLattice_416 (coe v1)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.isPartialOrder
d_isPartialOrder_552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_552 ~v0 ~v1 ~v2 v3 = du_isPartialOrder_552 v3
du_isPartialOrder_552 ::
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_isPartialOrder_552 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_430
         (coe d_isDistributiveLattice_526 (coe v0)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.isPreorder
d_isPreorder_554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_554 ~v0 ~v1 ~v2 v3 = du_isPreorder_554 v3
du_isPreorder_554 ::
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_isPreorder_554 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_430
            (coe d_isDistributiveLattice_526 (coe v0))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.joinSemilattice
d_joinSemilattice_556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 -> T_JoinSemilattice_14
d_joinSemilattice_556 ~v0 ~v1 ~v2 v3 = du_joinSemilattice_556 v3
du_joinSemilattice_556 ::
  T_DistributiveLattice_496 -> T_JoinSemilattice_14
du_joinSemilattice_556 v0
  = coe du_joinSemilattice_480 (coe du_lattice_536 (coe v0))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.meetSemilattice
d_meetSemilattice_558 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 -> T_MeetSemilattice_200
d_meetSemilattice_558 ~v0 ~v1 ~v2 v3 = du_meetSemilattice_558 v3
du_meetSemilattice_558 ::
  T_DistributiveLattice_496 -> T_MeetSemilattice_200
du_meetSemilattice_558 v0
  = coe du_meetSemilattice_482 (coe du_lattice_536 (coe v0))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.poset
d_poset_560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_560 ~v0 ~v1 ~v2 v3 = du_poset_560 v3
du_poset_560 ::
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_560 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe (coe du_poset_90 (coe du_joinSemilattice_480 (coe v1)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.preorder
d_preorder_562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_preorder_562 ~v0 ~v1 ~v2 v3 = du_preorder_562 v3
du_preorder_562 ::
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_preorder_562 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = coe du_joinSemilattice_480 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344
            (coe du_poset_90 (coe v2))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.refl
d_refl_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 -> AgdaAny -> AgdaAny
d_refl_564 ~v0 ~v1 ~v2 v3 = du_refl_564 v3
du_refl_564 :: T_DistributiveLattice_496 -> AgdaAny -> AgdaAny
du_refl_564 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_98
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.reflexive
d_reflexive_566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_566 ~v0 ~v1 ~v2 v3 = du_reflexive_566 v3
du_reflexive_566 ::
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_566 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_430
               (coe d_isDistributiveLattice_526 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.setoid
d_setoid_568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_568 ~v0 ~v1 ~v2 v3 = du_setoid_568 v3
du_setoid_568 ::
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_568 v0 = coe du_setoid_478 (coe du_lattice_536 (coe v0))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.supremum
d_supremum_570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_570 ~v0 ~v1 ~v2 v3 = du_supremum_570 v3
du_supremum_570 ::
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_supremum_570 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_supremum_354
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_430
         (coe d_isDistributiveLattice_526 (coe v0)))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.trans
d_trans_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_572 ~v0 ~v1 ~v2 v3 = du_trans_572 v3
du_trans_572 ::
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_572 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_430
               (coe d_isDistributiveLattice_526 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.x∧y≤x
d_x'8743'y'8804'x_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_574 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'x_574 v3
du_x'8743'y'8804'x_574 ::
  T_DistributiveLattice_496 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_574 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'x_196
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.x∧y≤y
d_x'8743'y'8804'y_576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_576 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'y_576 v3
du_x'8743'y'8804'y_576 ::
  T_DistributiveLattice_496 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_576 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'y_208
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.x≤x∨y
d_x'8804'x'8744'y_578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_578 ~v0 ~v1 ~v2 v3 = du_x'8804'x'8744'y_578 v3
du_x'8804'x'8744'y_578 ::
  T_DistributiveLattice_496 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_578 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.y≤x∨y
d_y'8804'x'8744'y_580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_580 ~v0 ~v1 ~v2 v3 = du_y'8804'x'8744'y_580 v3
du_y'8804'x'8744'y_580 ::
  T_DistributiveLattice_496 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_580 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.∧-greatest
d_'8743''45'greatest_582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_582 ~v0 ~v1 ~v2 v3
  = du_'8743''45'greatest_582 v3
du_'8743''45'greatest_582 ::
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_582 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8743''45'greatest_222
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.∨-least
d_'8744''45'least_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_584 ~v0 ~v1 ~v2 v3 = du_'8744''45'least_584 v3
du_'8744''45'least_584 ::
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_584 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_586 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_586 v3
du_'8764''45'resp'45''8776'_586 ::
  T_DistributiveLattice_496 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_586 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_588 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_588 v3
du_'8764''45'resp'691''45''8776'_588 ::
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_588 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_590 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_590 v3
du_'8764''45'resp'737''45''8776'_590 ::
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_590 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_592 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_592 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_592 v3
du_'8818''45'resp'45''8776'_592 ::
  T_DistributiveLattice_496 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_592 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_594 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_594 v3
du_'8818''45'resp'691''45''8776'_594 ::
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_594 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_596 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_596 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_596 v3
du_'8818''45'resp'737''45''8776'_596 ::
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_596 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_600 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_600 v3
du_isPartialEquivalence_600 ::
  T_DistributiveLattice_496 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_600 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.Eq.refl
d_refl_602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 -> AgdaAny -> AgdaAny
d_refl_602 ~v0 ~v1 ~v2 v3 = du_refl_602 v3
du_refl_602 :: T_DistributiveLattice_496 -> AgdaAny -> AgdaAny
du_refl_602 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_430
                  (coe d_isDistributiveLattice_526 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.Eq.reflexive
d_reflexive_604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_604 ~v0 ~v1 ~v2 v3 = du_reflexive_604 v3
du_reflexive_604 ::
  T_DistributiveLattice_496 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_604 v0
  = let v1 = coe du_lattice_536 (coe v0) in
    coe
      (let v2 = d_isLattice_416 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.Eq.sym
d_sym_606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_606 ~v0 ~v1 ~v2 v3 = du_sym_606 v3
du_sym_606 ::
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_606 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_430
                  (coe d_isDistributiveLattice_526 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.DistributiveLattice._.Eq.trans
d_trans_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_608 ~v0 ~v1 ~v2 v3 = du_trans_608 v3
du_trans_608 ::
  T_DistributiveLattice_496 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_608 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_430
                  (coe d_isDistributiveLattice_526 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice
d_BoundedLattice_616 a0 a1 a2 = ()
data T_BoundedLattice_616
  = C_BoundedLattice'46'constructor_14911 (AgdaAny ->
                                           AgdaAny -> AgdaAny)
                                          (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny AgdaAny
                                          MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedLattice_502
-- Relation.Binary.Lattice.Bundles.BoundedLattice.Carrier
d_Carrier_640 :: T_BoundedLattice_616 -> ()
d_Carrier_640 = erased
-- Relation.Binary.Lattice.Bundles.BoundedLattice._≈_
d__'8776'__642 :: T_BoundedLattice_616 -> AgdaAny -> AgdaAny -> ()
d__'8776'__642 = erased
-- Relation.Binary.Lattice.Bundles.BoundedLattice._≤_
d__'8804'__644 :: T_BoundedLattice_616 -> AgdaAny -> AgdaAny -> ()
d__'8804'__644 = erased
-- Relation.Binary.Lattice.Bundles.BoundedLattice._∨_
d__'8744'__646 ::
  T_BoundedLattice_616 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__646 v0
  = case coe v0 of
      C_BoundedLattice'46'constructor_14911 v4 v5 v6 v7 v8 -> coe v4
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedLattice._∧_
d__'8743'__648 ::
  T_BoundedLattice_616 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__648 v0
  = case coe v0 of
      C_BoundedLattice'46'constructor_14911 v4 v5 v6 v7 v8 -> coe v5
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedLattice.⊤
d_'8868'_650 :: T_BoundedLattice_616 -> AgdaAny
d_'8868'_650 v0
  = case coe v0 of
      C_BoundedLattice'46'constructor_14911 v4 v5 v6 v7 v8 -> coe v6
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedLattice.⊥
d_'8869'_652 :: T_BoundedLattice_616 -> AgdaAny
d_'8869'_652 v0
  = case coe v0 of
      C_BoundedLattice'46'constructor_14911 v4 v5 v6 v7 v8 -> coe v7
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedLattice.isBoundedLattice
d_isBoundedLattice_654 ::
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedLattice_502
d_isBoundedLattice_654 v0
  = case coe v0 of
      C_BoundedLattice'46'constructor_14911 v4 v5 v6 v7 v8 -> coe v8
      _                                                    -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.antisym
d_antisym_658 ::
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_658 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
            (coe d_isBoundedLattice_654 (coe v0))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.infimum
d_infimum_660 ::
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_660 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_infimum_356
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
         (coe d_isBoundedLattice_654 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_662 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_116
d_isBoundedJoinSemilattice_662 ~v0 ~v1 ~v2 v3
  = du_isBoundedJoinSemilattice_662 v3
du_isBoundedJoinSemilattice_662 ::
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_116
du_isBoundedJoinSemilattice_662 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedJoinSemilattice_584
      (coe d_isBoundedLattice_654 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_664 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_274
d_isBoundedMeetSemilattice_664 ~v0 ~v1 ~v2 v3
  = du_isBoundedMeetSemilattice_664 v3
du_isBoundedMeetSemilattice_664 ::
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_274
du_isBoundedMeetSemilattice_664 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedMeetSemilattice_586
      (coe d_isBoundedLattice_654 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isEquivalence
d_isEquivalence_666 ::
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_666 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
               (coe d_isBoundedLattice_654 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isJoinSemilattice
d_isJoinSemilattice_668 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_isJoinSemilattice_668 ~v0 ~v1 ~v2 v3
  = du_isJoinSemilattice_668 v3
du_isJoinSemilattice_668 ::
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_isJoinSemilattice_668 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isLattice
d_isLattice_670 ::
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
d_isLattice_670 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
      (coe d_isBoundedLattice_654 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isMeetSemilattice
d_isMeetSemilattice_672 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
d_isMeetSemilattice_672 ~v0 ~v1 ~v2 v3
  = du_isMeetSemilattice_672 v3
du_isMeetSemilattice_672 ::
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
du_isMeetSemilattice_672 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
            (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isPartialOrder
d_isPartialOrder_674 ::
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_674 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
         (coe d_isBoundedLattice_654 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.isPreorder
d_isPreorder_676 ::
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_676 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
            (coe d_isBoundedLattice_654 (coe v0))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.maximum
d_maximum_678 :: T_BoundedLattice_616 -> AgdaAny -> AgdaAny
d_maximum_678 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_maximum_520
      (coe d_isBoundedLattice_654 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.minimum
d_minimum_680 :: T_BoundedLattice_616 -> AgdaAny -> AgdaAny
d_minimum_680 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_minimum_522
      (coe d_isBoundedLattice_654 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.refl
d_refl_682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 -> AgdaAny -> AgdaAny
d_refl_682 ~v0 ~v1 ~v2 v3 = du_refl_682 v3
du_refl_682 :: T_BoundedLattice_616 -> AgdaAny -> AgdaAny
du_refl_682 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_refl_98
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.reflexive
d_reflexive_684 ::
  T_BoundedLattice_616 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_684 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
               (coe d_isBoundedLattice_654 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.supremum
d_supremum_686 ::
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_686 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_supremum_354
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
         (coe d_isBoundedLattice_654 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.trans
d_trans_688 ::
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_688 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
               (coe d_isBoundedLattice_654 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.x∧y≤x
d_x'8743'y'8804'x_690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_690 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'x_690 v3
du_x'8743'y'8804'x_690 ::
  T_BoundedLattice_616 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_690 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'x_196
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.x∧y≤y
d_x'8743'y'8804'y_692 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_692 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'y_692 v3
du_x'8743'y'8804'y_692 ::
  T_BoundedLattice_616 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_692 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'y_208
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.x≤x∨y
d_x'8804'x'8744'y_694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_694 ~v0 ~v1 ~v2 v3 = du_x'8804'x'8744'y_694 v3
du_x'8804'x'8744'y_694 ::
  T_BoundedLattice_616 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_694 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.y≤x∨y
d_y'8804'x'8744'y_696 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_696 ~v0 ~v1 ~v2 v3 = du_y'8804'x'8744'y_696 v3
du_y'8804'x'8744'y_696 ::
  T_BoundedLattice_616 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_696 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.∧-greatest
d_'8743''45'greatest_698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_698 ~v0 ~v1 ~v2 v3
  = du_'8743''45'greatest_698 v3
du_'8743''45'greatest_698 ::
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_698 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8743''45'greatest_222
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.∨-least
d_'8744''45'least_700 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_700 ~v0 ~v1 ~v2 v3 = du_'8744''45'least_700 v3
du_'8744''45'least_700 ::
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_700 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.∼-resp-≈
d_'8764''45'resp'45''8776'_702 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_702 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_702 v3
du_'8764''45'resp'45''8776'_702 ::
  T_BoundedLattice_616 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_702 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_704 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_704 v3
du_'8764''45'resp'691''45''8776'_704 ::
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_704 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_706 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_706 v3
du_'8764''45'resp'737''45''8776'_706 ::
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_706 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.≲-resp-≈
d_'8818''45'resp'45''8776'_708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_708 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_708 v3
du_'8818''45'resp'45''8776'_708 ::
  T_BoundedLattice_616 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_708 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_710 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_710 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_710 v3
du_'8818''45'resp'691''45''8776'_710 ::
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_710 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_712 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_712 v3
du_'8818''45'resp'737''45''8776'_712 ::
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_712 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.Eq.isPartialEquivalence
d_isPartialEquivalence_716 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_716 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_716 v3
du_isPartialEquivalence_716 ::
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_716 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.Eq.refl
d_refl_718 :: T_BoundedLattice_616 -> AgdaAny -> AgdaAny
d_refl_718 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                  (coe d_isBoundedLattice_654 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.Eq.reflexive
d_reflexive_720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_720 ~v0 ~v1 ~v2 v3 = du_reflexive_720 v3
du_reflexive_720 ::
  T_BoundedLattice_616 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_720 v0
  = let v1 = d_isBoundedLattice_654 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                    (coe v2) in
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
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.Eq.sym
d_sym_722 ::
  T_BoundedLattice_616 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_722 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                  (coe d_isBoundedLattice_654 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.Eq.trans
d_trans_724 ::
  T_BoundedLattice_616 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_724 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                  (coe d_isBoundedLattice_654 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice.boundedJoinSemilattice
d_boundedJoinSemilattice_726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 -> T_BoundedJoinSemilattice_102
d_boundedJoinSemilattice_726 ~v0 ~v1 ~v2 v3
  = du_boundedJoinSemilattice_726 v3
du_boundedJoinSemilattice_726 ::
  T_BoundedLattice_616 -> T_BoundedJoinSemilattice_102
du_boundedJoinSemilattice_726 v0
  = coe
      C_BoundedJoinSemilattice'46'constructor_2401
      (d__'8744'__646 (coe v0)) (d_'8869'_652 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedJoinSemilattice_584
         (coe d_isBoundedLattice_654 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice.boundedMeetSemilattice
d_boundedMeetSemilattice_728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 -> T_BoundedMeetSemilattice_288
d_boundedMeetSemilattice_728 ~v0 ~v1 ~v2 v3
  = du_boundedMeetSemilattice_728 v3
du_boundedMeetSemilattice_728 ::
  T_BoundedLattice_616 -> T_BoundedMeetSemilattice_288
du_boundedMeetSemilattice_728 v0
  = coe
      C_BoundedMeetSemilattice'46'constructor_6659
      (d__'8743'__648 (coe v0)) (d_'8868'_650 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedMeetSemilattice_586
         (coe d_isBoundedLattice_654 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice.lattice
d_lattice_730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 -> T_Lattice_386
d_lattice_730 ~v0 ~v1 ~v2 v3 = du_lattice_730 v3
du_lattice_730 :: T_BoundedLattice_616 -> T_Lattice_386
du_lattice_730 v0
  = coe
      C_Lattice'46'constructor_8977 (d__'8744'__646 (coe v0))
      (d__'8743'__648 (coe v0))
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
         (coe d_isBoundedLattice_654 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.joinSemilattice
d_joinSemilattice_734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 -> T_JoinSemilattice_14
d_joinSemilattice_734 ~v0 ~v1 ~v2 v3 = du_joinSemilattice_734 v3
du_joinSemilattice_734 ::
  T_BoundedLattice_616 -> T_JoinSemilattice_14
du_joinSemilattice_734 v0
  = coe du_joinSemilattice_480 (coe du_lattice_730 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.meetSemilattice
d_meetSemilattice_736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 -> T_MeetSemilattice_200
d_meetSemilattice_736 ~v0 ~v1 ~v2 v3 = du_meetSemilattice_736 v3
du_meetSemilattice_736 ::
  T_BoundedLattice_616 -> T_MeetSemilattice_200
du_meetSemilattice_736 v0
  = coe du_meetSemilattice_482 (coe du_lattice_730 (coe v0))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.poset
d_poset_738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_738 ~v0 ~v1 ~v2 v3 = du_poset_738 v3
du_poset_738 ::
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_738 v0
  = let v1 = coe du_lattice_730 (coe v0) in
    coe (coe du_poset_90 (coe du_joinSemilattice_480 (coe v1)))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.preorder
d_preorder_740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_preorder_740 ~v0 ~v1 ~v2 v3 = du_preorder_740 v3
du_preorder_740 ::
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_preorder_740 v0
  = let v1 = coe du_lattice_730 (coe v0) in
    coe
      (let v2 = coe du_joinSemilattice_480 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344
            (coe du_poset_90 (coe v2))))
-- Relation.Binary.Lattice.Bundles.BoundedLattice._.setoid
d_setoid_742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_742 ~v0 ~v1 ~v2 v3 = du_setoid_742 v3
du_setoid_742 ::
  T_BoundedLattice_616 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_742 v0 = coe du_setoid_478 (coe du_lattice_730 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra
d_HeytingAlgebra_750 a0 a1 a2 = ()
data T_HeytingAlgebra_750
  = C_HeytingAlgebra'46'constructor_18655 (AgdaAny ->
                                           AgdaAny -> AgdaAny)
                                          (AgdaAny -> AgdaAny -> AgdaAny)
                                          (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny AgdaAny
                                          MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsHeytingAlgebra_598
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra.Carrier
d_Carrier_776 :: T_HeytingAlgebra_750 -> ()
d_Carrier_776 = erased
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._≈_
d__'8776'__778 :: T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> ()
d__'8776'__778 = erased
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._≤_
d__'8804'__780 :: T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> ()
d__'8804'__780 = erased
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._∨_
d__'8744'__782 ::
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__782 v0
  = case coe v0 of
      C_HeytingAlgebra'46'constructor_18655 v4 v5 v6 v7 v8 v9 -> coe v4
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._∧_
d__'8743'__784 ::
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__784 v0
  = case coe v0 of
      C_HeytingAlgebra'46'constructor_18655 v4 v5 v6 v7 v8 v9 -> coe v5
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._⇨_
d__'8680'__786 ::
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8680'__786 v0
  = case coe v0 of
      C_HeytingAlgebra'46'constructor_18655 v4 v5 v6 v7 v8 v9 -> coe v6
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra.⊤
d_'8868'_788 :: T_HeytingAlgebra_750 -> AgdaAny
d_'8868'_788 v0
  = case coe v0 of
      C_HeytingAlgebra'46'constructor_18655 v4 v5 v6 v7 v8 v9 -> coe v7
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra.⊥
d_'8869'_790 :: T_HeytingAlgebra_750 -> AgdaAny
d_'8869'_790 v0
  = case coe v0 of
      C_HeytingAlgebra'46'constructor_18655 v4 v5 v6 v7 v8 v9 -> coe v8
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra.isHeytingAlgebra
d_isHeytingAlgebra_792 ::
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsHeytingAlgebra_598
d_isHeytingAlgebra_792 v0
  = case coe v0 of
      C_HeytingAlgebra'46'constructor_18655 v4 v5 v6 v7 v8 v9 -> coe v9
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra.boundedLattice
d_boundedLattice_794 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> T_BoundedLattice_616
d_boundedLattice_794 ~v0 ~v1 ~v2 v3 = du_boundedLattice_794 v3
du_boundedLattice_794 ::
  T_HeytingAlgebra_750 -> T_BoundedLattice_616
du_boundedLattice_794 v0
  = coe
      C_BoundedLattice'46'constructor_14911 (d__'8744'__782 (coe v0))
      (d__'8743'__784 (coe v0)) (d_'8868'_788 (coe v0))
      (d_'8869'_790 (coe v0))
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
         (coe d_isHeytingAlgebra_792 (coe v0)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.exponential
d_exponential_798 ::
  T_HeytingAlgebra_750 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exponential_798 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_exponential_616
      (coe d_isHeytingAlgebra_792 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.transpose-⇨
d_transpose'45''8680'_800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8680'_800 ~v0 ~v1 ~v2 v3
  = du_transpose'45''8680'_800 v3
du_transpose'45''8680'_800 ::
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8680'_800 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_transpose'45''8680'_624
      (coe d_isHeytingAlgebra_792 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.transpose-∧
d_transpose'45''8743'_802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8743'_802 ~v0 ~v1 ~v2 v3
  = du_transpose'45''8743'_802 v3
du_transpose'45''8743'_802 ::
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8743'_802 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.du_transpose'45''8743'_640
      (coe d_isHeytingAlgebra_792 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.antisym
d_antisym_806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_806 ~v0 ~v1 ~v2 v3 = du_antisym_806 v3
du_antisym_806 ::
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_806 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
               (coe d_isHeytingAlgebra_792 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.boundedJoinSemilattice
d_boundedJoinSemilattice_808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> T_BoundedJoinSemilattice_102
d_boundedJoinSemilattice_808 ~v0 ~v1 ~v2 v3
  = du_boundedJoinSemilattice_808 v3
du_boundedJoinSemilattice_808 ::
  T_HeytingAlgebra_750 -> T_BoundedJoinSemilattice_102
du_boundedJoinSemilattice_808 v0
  = coe
      du_boundedJoinSemilattice_726 (coe du_boundedLattice_794 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.boundedMeetSemilattice
d_boundedMeetSemilattice_810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> T_BoundedMeetSemilattice_288
d_boundedMeetSemilattice_810 ~v0 ~v1 ~v2 v3
  = du_boundedMeetSemilattice_810 v3
du_boundedMeetSemilattice_810 ::
  T_HeytingAlgebra_750 -> T_BoundedMeetSemilattice_288
du_boundedMeetSemilattice_810 v0
  = coe
      du_boundedMeetSemilattice_728 (coe du_boundedLattice_794 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.infimum
d_infimum_812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_812 ~v0 ~v1 ~v2 v3 = du_infimum_812 v3
du_infimum_812 ::
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infimum_812 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_infimum_356
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
            (coe d_isHeytingAlgebra_792 (coe v0))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_116
d_isBoundedJoinSemilattice_814 ~v0 ~v1 ~v2 v3
  = du_isBoundedJoinSemilattice_814 v3
du_isBoundedJoinSemilattice_814 ::
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_116
du_isBoundedJoinSemilattice_814 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedJoinSemilattice_584
         (coe d_isBoundedLattice_654 (coe v1)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isBoundedLattice
d_isBoundedLattice_816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedLattice_502
d_isBoundedLattice_816 ~v0 ~v1 ~v2 v3 = du_isBoundedLattice_816 v3
du_isBoundedLattice_816 ::
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedLattice_502
du_isBoundedLattice_816 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
      (coe d_isHeytingAlgebra_792 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_274
d_isBoundedMeetSemilattice_818 ~v0 ~v1 ~v2 v3
  = du_isBoundedMeetSemilattice_818 v3
du_isBoundedMeetSemilattice_818 ::
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_274
du_isBoundedMeetSemilattice_818 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedMeetSemilattice_586
         (coe d_isBoundedLattice_654 (coe v1)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isEquivalence
d_isEquivalence_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_820 ~v0 ~v1 ~v2 v3 = du_isEquivalence_820 v3
du_isEquivalence_820 ::
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_820 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
                  (coe d_isHeytingAlgebra_792 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isJoinSemilattice
d_isJoinSemilattice_822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_isJoinSemilattice_822 ~v0 ~v1 ~v2 v3
  = du_isJoinSemilattice_822 v3
du_isJoinSemilattice_822 ::
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_isJoinSemilattice_822 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isLattice
d_isLattice_824 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
d_isLattice_824 ~v0 ~v1 ~v2 v3 = du_isLattice_824 v3
du_isLattice_824 ::
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
du_isLattice_824 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
         (coe d_isHeytingAlgebra_792 (coe v0)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isMeetSemilattice
d_isMeetSemilattice_826 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
d_isMeetSemilattice_826 ~v0 ~v1 ~v2 v3
  = du_isMeetSemilattice_826 v3
du_isMeetSemilattice_826 ::
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
du_isMeetSemilattice_826 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
               (coe v2))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isPartialOrder
d_isPartialOrder_828 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_828 ~v0 ~v1 ~v2 v3 = du_isPartialOrder_828 v3
du_isPartialOrder_828 ::
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_isPartialOrder_828 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
            (coe d_isHeytingAlgebra_792 (coe v0))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.isPreorder
d_isPreorder_830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_830 ~v0 ~v1 ~v2 v3 = du_isPreorder_830 v3
du_isPreorder_830 ::
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_isPreorder_830 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
               (coe d_isHeytingAlgebra_792 (coe v0)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.joinSemilattice
d_joinSemilattice_832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> T_JoinSemilattice_14
d_joinSemilattice_832 ~v0 ~v1 ~v2 v3 = du_joinSemilattice_832 v3
du_joinSemilattice_832 ::
  T_HeytingAlgebra_750 -> T_JoinSemilattice_14
du_joinSemilattice_832 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe (coe du_joinSemilattice_480 (coe du_lattice_730 (coe v1)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.lattice
d_lattice_834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> T_Lattice_386
d_lattice_834 ~v0 ~v1 ~v2 v3 = du_lattice_834 v3
du_lattice_834 :: T_HeytingAlgebra_750 -> T_Lattice_386
du_lattice_834 v0
  = coe du_lattice_730 (coe du_boundedLattice_794 (coe v0))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.maximum
d_maximum_836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny
d_maximum_836 ~v0 ~v1 ~v2 v3 = du_maximum_836 v3
du_maximum_836 :: T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny
du_maximum_836 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_maximum_520
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
         (coe d_isHeytingAlgebra_792 (coe v0)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.meetSemilattice
d_meetSemilattice_838 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> T_MeetSemilattice_200
d_meetSemilattice_838 ~v0 ~v1 ~v2 v3 = du_meetSemilattice_838 v3
du_meetSemilattice_838 ::
  T_HeytingAlgebra_750 -> T_MeetSemilattice_200
du_meetSemilattice_838 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe (coe du_meetSemilattice_482 (coe du_lattice_730 (coe v1)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.minimum
d_minimum_840 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny
d_minimum_840 ~v0 ~v1 ~v2 v3 = du_minimum_840 v3
du_minimum_840 :: T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny
du_minimum_840 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_minimum_522
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
         (coe d_isHeytingAlgebra_792 (coe v0)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.poset
d_poset_842 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_842 ~v0 ~v1 ~v2 v3 = du_poset_842 v3
du_poset_842 ::
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_842 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = coe du_lattice_730 (coe v1) in
       coe (coe du_poset_90 (coe du_joinSemilattice_480 (coe v2))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.preorder
d_preorder_844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_preorder_844 ~v0 ~v1 ~v2 v3 = du_preorder_844 v3
du_preorder_844 ::
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_preorder_844 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = coe du_lattice_730 (coe v1) in
       coe
         (let v3 = coe du_joinSemilattice_480 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344
               (coe du_poset_90 (coe v3)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.refl
d_refl_846 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny
d_refl_846 ~v0 ~v1 ~v2 v3 = du_refl_846 v3
du_refl_846 :: T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny
du_refl_846 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.reflexive
d_reflexive_848 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_848 ~v0 ~v1 ~v2 v3 = du_reflexive_848 v3
du_reflexive_848 ::
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_848 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
                  (coe d_isHeytingAlgebra_792 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.setoid
d_setoid_850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_850 ~v0 ~v1 ~v2 v3 = du_setoid_850 v3
du_setoid_850 ::
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_850 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe (coe du_setoid_478 (coe du_lattice_730 (coe v1)))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.supremum
d_supremum_852 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_852 ~v0 ~v1 ~v2 v3 = du_supremum_852 v3
du_supremum_852 ::
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_supremum_852 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_supremum_354
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
            (coe d_isHeytingAlgebra_792 (coe v0))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.trans
d_trans_854 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_854 ~v0 ~v1 ~v2 v3 = du_trans_854 v3
du_trans_854 ::
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_854 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
                  (coe d_isHeytingAlgebra_792 (coe v0))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.x∧y≤x
d_x'8743'y'8804'x_856 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_856 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'x_856 v3
du_x'8743'y'8804'x_856 ::
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_856 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'x_196
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.x∧y≤y
d_x'8743'y'8804'y_858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_858 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'y_858 v3
du_x'8743'y'8804'y_858 ::
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_858 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'y_208
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.x≤x∨y
d_x'8804'x'8744'y_860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_860 ~v0 ~v1 ~v2 v3 = du_x'8804'x'8744'y_860 v3
du_x'8804'x'8744'y_860 ::
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_860 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.y≤x∨y
d_y'8804'x'8744'y_862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_862 ~v0 ~v1 ~v2 v3 = du_y'8804'x'8744'y_862 v3
du_y'8804'x'8744'y_862 ::
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_862 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.∧-greatest
d_'8743''45'greatest_864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_864 ~v0 ~v1 ~v2 v3
  = du_'8743''45'greatest_864 v3
du_'8743''45'greatest_864 ::
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_864 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8743''45'greatest_222
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.∨-least
d_'8744''45'least_866 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_866 ~v0 ~v1 ~v2 v3 = du_'8744''45'least_866 v3
du_'8744''45'least_866 ::
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_866 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.∼-resp-≈
d_'8764''45'resp'45''8776'_868 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_868 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_868 v3
du_'8764''45'resp'45''8776'_868 ::
  T_HeytingAlgebra_750 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_868 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_870 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_870 v3
du_'8764''45'resp'691''45''8776'_870 ::
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_870 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_872 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_872 v3
du_'8764''45'resp'737''45''8776'_872 ::
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_872 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.≲-resp-≈
d_'8818''45'resp'45''8776'_874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_874 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_874 v3
du_'8818''45'resp'45''8776'_874 ::
  T_HeytingAlgebra_750 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_874 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_876 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_876 v3
du_'8818''45'resp'691''45''8776'_876 ::
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_876 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_878 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_878 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_878 v3
du_'8818''45'resp'737''45''8776'_878 ::
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_878 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.Eq.isPartialEquivalence
d_isPartialEquivalence_882 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_882 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_882 v3
du_isPartialEquivalence_882 ::
  T_HeytingAlgebra_750 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_882 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                       (coe v3) in
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
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.Eq.refl
d_refl_884 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny
d_refl_884 ~v0 ~v1 ~v2 v3 = du_refl_884 v3
du_refl_884 :: T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny
du_refl_884 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
                     (coe d_isHeytingAlgebra_792 (coe v0)))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.Eq.reflexive
d_reflexive_886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_886 ~v0 ~v1 ~v2 v3 = du_reflexive_886 v3
du_reflexive_886 ::
  T_HeytingAlgebra_750 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_886 v0
  = let v1 = coe du_boundedLattice_794 (coe v0) in
    coe
      (let v2 = d_isBoundedLattice_654 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                       (coe v3) in
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
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.Eq.sym
d_sym_888 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_888 ~v0 ~v1 ~v2 v3 = du_sym_888 v3
du_sym_888 ::
  T_HeytingAlgebra_750 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_888 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
                     (coe d_isHeytingAlgebra_792 (coe v0)))))))
-- Relation.Binary.Lattice.Bundles.HeytingAlgebra._.Eq.trans
d_trans_890 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_890 ~v0 ~v1 ~v2 v3 = du_trans_890 v3
du_trans_890 ::
  T_HeytingAlgebra_750 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_890 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
                     (coe d_isHeytingAlgebra_792 (coe v0)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra
d_BooleanAlgebra_898 a0 a1 a2 = ()
data T_BooleanAlgebra_898
  = C_BooleanAlgebra'46'constructor_22683 (AgdaAny ->
                                           AgdaAny -> AgdaAny)
                                          (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                          AgdaAny AgdaAny
                                          MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBooleanAlgebra_730
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra.Carrier
d_Carrier_924 :: T_BooleanAlgebra_898 -> ()
d_Carrier_924 = erased
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._≈_
d__'8776'__926 :: T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> ()
d__'8776'__926 = erased
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._≤_
d__'8804'__928 :: T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> ()
d__'8804'__928 = erased
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._∨_
d__'8744'__930 ::
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__930 v0
  = case coe v0 of
      C_BooleanAlgebra'46'constructor_22683 v4 v5 v6 v7 v8 v9 -> coe v4
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._∧_
d__'8743'__932 ::
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__932 v0
  = case coe v0 of
      C_BooleanAlgebra'46'constructor_22683 v4 v5 v6 v7 v8 v9 -> coe v5
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra.¬_
d_'172'__934 :: T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny
d_'172'__934 v0
  = case coe v0 of
      C_BooleanAlgebra'46'constructor_22683 v4 v5 v6 v7 v8 v9 -> coe v6
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra.⊤
d_'8868'_936 :: T_BooleanAlgebra_898 -> AgdaAny
d_'8868'_936 v0
  = case coe v0 of
      C_BooleanAlgebra'46'constructor_22683 v4 v5 v6 v7 v8 v9 -> coe v7
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra.⊥
d_'8869'_938 :: T_BooleanAlgebra_898 -> AgdaAny
d_'8869'_938 v0
  = case coe v0 of
      C_BooleanAlgebra'46'constructor_22683 v4 v5 v6 v7 v8 v9 -> coe v8
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra.isBooleanAlgebra
d_isBooleanAlgebra_940 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBooleanAlgebra_730
d_isBooleanAlgebra_940 v0
  = case coe v0 of
      C_BooleanAlgebra'46'constructor_22683 v4 v5 v6 v7 v8 v9 -> coe v9
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra.heytingAlgebra
d_heytingAlgebra_946 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> T_HeytingAlgebra_750
d_heytingAlgebra_946 ~v0 ~v1 ~v2 v3 = du_heytingAlgebra_946 v3
du_heytingAlgebra_946 ::
  T_BooleanAlgebra_898 -> T_HeytingAlgebra_750
du_heytingAlgebra_946 v0
  = coe
      C_HeytingAlgebra'46'constructor_18655 (d__'8744'__930 (coe v0))
      (d__'8743'__932 (coe v0))
      (\ v1 -> coe d__'8744'__930 v0 (coe d_'172'__934 v0 v1))
      (d_'8868'_936 (coe v0)) (d_'8869'_938 (coe v0))
      (MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isHeytingAlgebra_756
         (coe d_isBooleanAlgebra_940 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._._⇨_
d__'8680'__950 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8680'__950 ~v0 ~v1 ~v2 v3 v4 = du__'8680'__950 v3 v4
du__'8680'__950 ::
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny
du__'8680'__950 v0 v1
  = coe d__'8744'__930 v0 (coe d_'172'__934 v0 v1)
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.antisym
d_antisym_952 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_952 ~v0 ~v1 ~v2 v3 = du_antisym_952 v3
du_antisym_952 ::
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_952 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_antisym_184
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
                  (coe d_isHeytingAlgebra_792 (coe v1))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.boundedJoinSemilattice
d_boundedJoinSemilattice_954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> T_BoundedJoinSemilattice_102
d_boundedJoinSemilattice_954 ~v0 ~v1 ~v2 v3
  = du_boundedJoinSemilattice_954 v3
du_boundedJoinSemilattice_954 ::
  T_BooleanAlgebra_898 -> T_BoundedJoinSemilattice_102
du_boundedJoinSemilattice_954 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         du_boundedJoinSemilattice_726 (coe du_boundedLattice_794 (coe v1)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.boundedLattice
d_boundedLattice_956 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> T_BoundedLattice_616
d_boundedLattice_956 ~v0 ~v1 ~v2 v3 = du_boundedLattice_956 v3
du_boundedLattice_956 ::
  T_BooleanAlgebra_898 -> T_BoundedLattice_616
du_boundedLattice_956 v0
  = coe du_boundedLattice_794 (coe du_heytingAlgebra_946 (coe v0))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.boundedMeetSemilattice
d_boundedMeetSemilattice_958 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> T_BoundedMeetSemilattice_288
d_boundedMeetSemilattice_958 ~v0 ~v1 ~v2 v3
  = du_boundedMeetSemilattice_958 v3
du_boundedMeetSemilattice_958 ::
  T_BooleanAlgebra_898 -> T_BoundedMeetSemilattice_288
du_boundedMeetSemilattice_958 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         du_boundedMeetSemilattice_728 (coe du_boundedLattice_794 (coe v1)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.exponential
d_exponential_960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_exponential_960 ~v0 ~v1 ~v2 v3 = du_exponential_960 v3
du_exponential_960 ::
  T_BooleanAlgebra_898 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_exponential_960 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_exponential_616
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isHeytingAlgebra_756
         (coe d_isBooleanAlgebra_940 (coe v0)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.infimum
d_infimum_962 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_infimum_962 ~v0 ~v1 ~v2 v3 = du_infimum_962 v3
du_infimum_962 ::
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_infimum_962 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_infimum_356
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
               (coe d_isHeytingAlgebra_792 (coe v1)))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_964 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_116
d_isBoundedJoinSemilattice_964 ~v0 ~v1 ~v2 v3
  = du_isBoundedJoinSemilattice_964 v3
du_isBoundedJoinSemilattice_964 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedJoinSemilattice_116
du_isBoundedJoinSemilattice_964 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedJoinSemilattice_584
            (coe d_isBoundedLattice_654 (coe v2))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isBoundedLattice
d_isBoundedLattice_966 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedLattice_502
d_isBoundedLattice_966 ~v0 ~v1 ~v2 v3 = du_isBoundedLattice_966 v3
du_isBoundedLattice_966 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedLattice_502
du_isBoundedLattice_966 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
         (coe d_isHeytingAlgebra_792 (coe v1)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_968 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_274
d_isBoundedMeetSemilattice_968 ~v0 ~v1 ~v2 v3
  = du_isBoundedMeetSemilattice_968 v3
du_isBoundedMeetSemilattice_968 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsBoundedMeetSemilattice_274
du_isBoundedMeetSemilattice_968 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isBoundedMeetSemilattice_586
            (coe d_isBoundedLattice_654 (coe v2))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isEquivalence
d_isEquivalence_970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_970 ~v0 ~v1 ~v2 v3 = du_isEquivalence_970 v3
du_isEquivalence_970 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_970 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
                     (coe d_isHeytingAlgebra_792 (coe v1)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isHeytingAlgebra
d_isHeytingAlgebra_972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsHeytingAlgebra_598
d_isHeytingAlgebra_972 ~v0 ~v1 ~v2 v3 = du_isHeytingAlgebra_972 v3
du_isHeytingAlgebra_972 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsHeytingAlgebra_598
du_isHeytingAlgebra_972 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isHeytingAlgebra_756
      (coe d_isBooleanAlgebra_940 (coe v0))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isJoinSemilattice
d_isJoinSemilattice_974 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_isJoinSemilattice_974 ~v0 ~v1 ~v2 v3
  = du_isJoinSemilattice_974 v3
du_isJoinSemilattice_974 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_isJoinSemilattice_974 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isLattice
d_isLattice_976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
d_isLattice_976 ~v0 ~v1 ~v2 v3 = du_isLattice_976 v3
du_isLattice_976 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
du_isLattice_976 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
            (coe d_isHeytingAlgebra_792 (coe v1))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isMeetSemilattice
d_isMeetSemilattice_978 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
d_isMeetSemilattice_978 ~v0 ~v1 ~v2 v3
  = du_isMeetSemilattice_978 v3
du_isMeetSemilattice_978 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
du_isMeetSemilattice_978 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                  (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isPartialOrder
d_isPartialOrder_980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_980 ~v0 ~v1 ~v2 v3 = du_isPartialOrder_980 v3
du_isPartialOrder_980 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_isPartialOrder_980 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
               (coe d_isHeytingAlgebra_792 (coe v1)))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.isPreorder
d_isPreorder_982 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_982 ~v0 ~v1 ~v2 v3 = du_isPreorder_982 v3
du_isPreorder_982 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_isPreorder_982 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
                  (coe d_isHeytingAlgebra_792 (coe v1))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.joinSemilattice
d_joinSemilattice_984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> T_JoinSemilattice_14
d_joinSemilattice_984 ~v0 ~v1 ~v2 v3 = du_joinSemilattice_984 v3
du_joinSemilattice_984 ::
  T_BooleanAlgebra_898 -> T_JoinSemilattice_14
du_joinSemilattice_984 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe (coe du_joinSemilattice_480 (coe du_lattice_730 (coe v2))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.lattice
d_lattice_986 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> T_Lattice_386
d_lattice_986 ~v0 ~v1 ~v2 v3 = du_lattice_986 v3
du_lattice_986 :: T_BooleanAlgebra_898 -> T_Lattice_386
du_lattice_986 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe (coe du_lattice_730 (coe du_boundedLattice_794 (coe v1)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.maximum
d_maximum_988 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny
d_maximum_988 ~v0 ~v1 ~v2 v3 = du_maximum_988 v3
du_maximum_988 :: T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny
du_maximum_988 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_maximum_520
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
            (coe d_isHeytingAlgebra_792 (coe v1))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.meetSemilattice
d_meetSemilattice_990 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> T_MeetSemilattice_200
d_meetSemilattice_990 ~v0 ~v1 ~v2 v3 = du_meetSemilattice_990 v3
du_meetSemilattice_990 ::
  T_BooleanAlgebra_898 -> T_MeetSemilattice_200
du_meetSemilattice_990 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe (coe du_meetSemilattice_482 (coe du_lattice_730 (coe v2))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.minimum
d_minimum_992 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny
d_minimum_992 ~v0 ~v1 ~v2 v3 = du_minimum_992 v3
du_minimum_992 :: T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny
du_minimum_992 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_minimum_522
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
            (coe d_isHeytingAlgebra_792 (coe v1))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.poset
d_poset_994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_994 ~v0 ~v1 ~v2 v3 = du_poset_994 v3
du_poset_994 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_994 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = coe du_lattice_730 (coe v2) in
          coe (coe du_poset_90 (coe du_joinSemilattice_480 (coe v3)))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.preorder
d_preorder_996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_preorder_996 ~v0 ~v1 ~v2 v3 = du_preorder_996 v3
du_preorder_996 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_preorder_996 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = coe du_lattice_730 (coe v2) in
          coe
            (let v4 = coe du_joinSemilattice_480 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.du_preorder_344
                  (coe du_poset_90 (coe v4))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.refl
d_refl_998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny
d_refl_998 ~v0 ~v1 ~v2 v3 = du_refl_998 v3
du_refl_998 :: T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny
du_refl_998 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.reflexive
d_reflexive_1000 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_1000 ~v0 ~v1 ~v2 v3 = du_reflexive_1000 v3
du_reflexive_1000 ::
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_1000 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
                     (coe d_isHeytingAlgebra_792 (coe v1)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.setoid
d_setoid_1002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_1002 ~v0 ~v1 ~v2 v3 = du_setoid_1002 v3
du_setoid_1002 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_1002 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe (coe du_setoid_478 (coe du_lattice_730 (coe v2))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.supremum
d_supremum_1004 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_1004 ~v0 ~v1 ~v2 v3 = du_supremum_1004 v3
du_supremum_1004 ::
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_supremum_1004 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.d_supremum_354
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
               (coe d_isHeytingAlgebra_792 (coe v1)))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.trans
d_trans_1006 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1006 ~v0 ~v1 ~v2 v3 = du_trans_1006 v3
du_trans_1006 ::
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1006 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_84
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
                     (coe d_isHeytingAlgebra_792 (coe v1)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.transpose-⇨
d_transpose'45''8680'_1008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8680'_1008 ~v0 ~v1 ~v2 v3
  = du_transpose'45''8680'_1008 v3
du_transpose'45''8680'_1008 ::
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8680'_1008 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_transpose'45''8680'_624
         (coe d_isHeytingAlgebra_792 (coe v1)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.transpose-∧
d_transpose'45''8743'_1010 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transpose'45''8743'_1010 ~v0 ~v1 ~v2 v3
  = du_transpose'45''8743'_1010 v3
du_transpose'45''8743'_1010 ::
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transpose'45''8743'_1010 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Lattice.Structures.du_transpose'45''8743'_640
         (coe d_isHeytingAlgebra_792 (coe v1)))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.x∧y≤x
d_x'8743'y'8804'x_1012 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'x_1012 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'x_1012 v3
du_x'8743'y'8804'x_1012 ::
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'x_1012 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'x_196
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.x∧y≤y
d_x'8743'y'8804'y_1014 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8743'y'8804'y_1014 ~v0 ~v1 ~v2 v3 = du_x'8743'y'8804'y_1014 v3
du_x'8743'y'8804'y_1014 ::
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8743'y'8804'y_1014 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8743'y'8804'y_208
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.x≤x∨y
d_x'8804'x'8744'y_1016 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'x'8744'y_1016 ~v0 ~v1 ~v2 v3 = du_x'8804'x'8744'y_1016 v3
du_x'8804'x'8744'y_1016 ::
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'x'8744'y_1016 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.y≤x∨y
d_y'8804'x'8744'y_1018 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8804'x'8744'y_1018 ~v0 ~v1 ~v2 v3 = du_y'8804'x'8744'y_1018 v3
du_y'8804'x'8744'y_1018 ::
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8804'x'8744'y_1018 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.∧-greatest
d_'8743''45'greatest_1020 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'greatest_1020 ~v0 ~v1 ~v2 v3
  = du_'8743''45'greatest_1020 v3
du_'8743''45'greatest_1020 ::
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'greatest_1020 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8743''45'greatest_222
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isMeetSemilattice_360
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.∨-least
d_'8744''45'least_1022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'least_1022 ~v0 ~v1 ~v2 v3 = du_'8744''45'least_1022 v3
du_'8744''45'least_1022 ::
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'least_1022 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.du_isJoinSemilattice_358
                     (coe v4))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.∼-resp-≈
d_'8764''45'resp'45''8776'_1024 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8764''45'resp'45''8776'_1024 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'45''8776'_1024 v3
du_'8764''45'resp'45''8776'_1024 ::
  T_BooleanAlgebra_898 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8764''45'resp'45''8776'_1024 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.∼-respʳ-≈
d_'8764''45'resp'691''45''8776'_1026 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'691''45''8776'_1026 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'691''45''8776'_1026 v3
du_'8764''45'resp'691''45''8776'_1026 ::
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'691''45''8776'_1026 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'691''45''8776'_116
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.∼-respˡ-≈
d_'8764''45'resp'737''45''8776'_1028 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8764''45'resp'737''45''8776'_1028 ~v0 ~v1 ~v2 v3
  = du_'8764''45'resp'737''45''8776'_1028 v3
du_'8764''45'resp'737''45''8776'_1028 ::
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8764''45'resp'737''45''8776'_1028 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'737''45''8776'_114
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.≲-resp-≈
d_'8818''45'resp'45''8776'_1030 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8818''45'resp'45''8776'_1030 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'45''8776'_1030 v3
du_'8818''45'resp'45''8776'_1030 ::
  T_BooleanAlgebra_898 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8818''45'resp'45''8776'_1030 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'45''8776'_112
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.≲-respʳ-≈
d_'8818''45'resp'691''45''8776'_1032 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'691''45''8776'_1032 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'691''45''8776'_1032 v3
du_'8818''45'resp'691''45''8776'_1032 ::
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'691''45''8776'_1032 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_106
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.≲-respˡ-≈
d_'8818''45'resp'737''45''8776'_1034 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8818''45'resp'737''45''8776'_1034 ~v0 ~v1 ~v2 v3
  = du_'8818''45'resp'737''45''8776'_1034 v3
du_'8818''45'resp'737''45''8776'_1034 ::
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8818''45'resp'737''45''8776'_1034 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_100
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                        (coe v5)))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.Eq.isPartialEquivalence
d_isPartialEquivalence_1038 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_1038 ~v0 ~v1 ~v2 v3
  = du_isPartialEquivalence_1038 v3
du_isPartialEquivalence_1038 ::
  T_BooleanAlgebra_898 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_1038 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                           (coe v6))))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.Eq.refl
d_refl_1040 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny
d_refl_1040 ~v0 ~v1 ~v2 v3 = du_refl_1040 v3
du_refl_1040 :: T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny
du_refl_1040 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                     (coe
                        MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
                        (coe d_isHeytingAlgebra_792 (coe v1))))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.Eq.reflexive
d_reflexive_1042 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_1042 ~v0 ~v1 ~v2 v3 = du_reflexive_1042 v3
du_reflexive_1042 ::
  T_BooleanAlgebra_898 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_1042 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (let v2 = coe du_boundedLattice_794 (coe v1) in
       coe
         (let v3 = d_isBoundedLattice_654 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
                             (coe v5) in
                   coe
                     (\ v7 v8 v9 ->
                        coe
                          MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
                             (coe v6))
                          v7))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.Eq.sym
d_sym_1044 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_1044 ~v0 ~v1 ~v2 v3 = du_sym_1044 v3
du_sym_1044 ::
  T_BooleanAlgebra_898 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_1044 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                     (coe
                        MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
                        (coe d_isHeytingAlgebra_792 (coe v1))))))))
-- Relation.Binary.Lattice.Bundles.BooleanAlgebra._.Eq.trans
d_trans_1046 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_1046 ~v0 ~v1 ~v2 v3 = du_trans_1046 v3
du_trans_1046 ::
  T_BooleanAlgebra_898 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_1046 v0
  = let v1 = coe du_heytingAlgebra_946 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182
               (coe
                  MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isPartialOrder_352
                  (coe
                     MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isLattice_518
                     (coe
                        MAlonzo.Code.Relation.Binary.Lattice.Structures.d_isBoundedLattice_614
                        (coe d_isHeytingAlgebra_792 (coe v1))))))))
