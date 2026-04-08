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

module MAlonzo.Code.Algebra.Lattice.Bundles where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Consequences.Base
import qualified MAlonzo.Code.Algebra.Lattice.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Lattice.Bundles.Semilattice
d_Semilattice_10 a0 a1 = ()
data T_Semilattice_10
  = C_constructor_84 (AgdaAny -> AgdaAny -> AgdaAny)
                     MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
-- Algebra.Lattice.Bundles.Semilattice.Carrier
d_Carrier_24 :: T_Semilattice_10 -> ()
d_Carrier_24 = erased
-- Algebra.Lattice.Bundles.Semilattice._≈_
d__'8776'__26 :: T_Semilattice_10 -> AgdaAny -> AgdaAny -> ()
d__'8776'__26 = erased
-- Algebra.Lattice.Bundles.Semilattice._∙_
d__'8729'__28 :: T_Semilattice_10 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__28 v0
  = case coe v0 of
      C_constructor_84 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.Semilattice.isSemilattice
d_isSemilattice_30 ::
  T_Semilattice_10 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isSemilattice_30 v0
  = case coe v0 of
      C_constructor_84 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.Semilattice._.assoc
d_assoc_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_34 ~v0 ~v1 v2 = du_assoc_34 v2
du_assoc_34 ::
  T_Semilattice_10 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_34 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))
-- Algebra.Lattice.Bundles.Semilattice._.comm
d_comm_36 :: T_Semilattice_10 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_36 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_622
      (coe d_isSemilattice_30 (coe v0))
-- Algebra.Lattice.Bundles.Semilattice._.idem
d_idem_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> AgdaAny -> AgdaAny
d_idem_38 ~v0 ~v1 v2 = du_idem_38 v2
du_idem_38 :: T_Semilattice_10 -> AgdaAny -> AgdaAny
du_idem_38 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_idem_536
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))
-- Algebra.Lattice.Bundles.Semilattice._.isBand
d_isBand_40 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_40 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isBand_620
      (coe d_isSemilattice_30 (coe v0))
-- Algebra.Lattice.Bundles.Semilattice._.isEquivalence
d_isEquivalence_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_42 ~v0 ~v1 v2 = du_isEquivalence_42 v2
du_isEquivalence_42 ::
  T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_42 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))))
-- Algebra.Lattice.Bundles.Semilattice._.isMagma
d_isMagma_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_44 ~v0 ~v1 v2 = du_isMagma_44 v2
du_isMagma_44 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_44 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))
-- Algebra.Lattice.Bundles.Semilattice._.isPartialEquivalence
d_isPartialEquivalence_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_46 ~v0 ~v1 v2
  = du_isPartialEquivalence_46 v2
du_isPartialEquivalence_46 ::
  T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_46 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v4))))))
-- Algebra.Lattice.Bundles.Semilattice._.isSemigroup
d_isSemigroup_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_48 ~v0 ~v1 v2 = du_isSemigroup_48 v2
du_isSemigroup_48 ::
  T_Semilattice_10 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_48 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))
-- Algebra.Lattice.Bundles.Semilattice._.refl
d_refl_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> AgdaAny -> AgdaAny
d_refl_50 ~v0 ~v1 v2 = du_refl_50 v2
du_refl_50 :: T_Semilattice_10 -> AgdaAny -> AgdaAny
du_refl_50 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Bundles.Semilattice._.reflexive
d_reflexive_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_52 ~v0 ~v1 v2 = du_reflexive_52 v2
du_reflexive_52 ::
  T_Semilattice_10 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_52 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v4))
                    v5))))
-- Algebra.Lattice.Bundles.Semilattice._.setoid
d_setoid_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_54 ~v0 ~v1 v2 = du_setoid_54 v2
du_setoid_54 ::
  T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_54 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_202
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3)))))
-- Algebra.Lattice.Bundles.Semilattice._.sym
d_sym_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_56 ~v0 ~v1 v2 = du_sym_56 v2
du_sym_56 ::
  T_Semilattice_10 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_56 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Bundles.Semilattice._.trans
d_trans_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_58 ~v0 ~v1 v2 = du_trans_58 v2
du_trans_58 ::
  T_Semilattice_10 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_58 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Bundles.Semilattice._.∙-cong
d_'8729''45'cong_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_60 ~v0 ~v1 v2 = du_'8729''45'cong_60 v2
du_'8729''45'cong_60 ::
  T_Semilattice_10 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_60 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))))
-- Algebra.Lattice.Bundles.Semilattice._.∙-congʳ
d_'8729''45'cong'691'_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_62 ~v0 ~v1 v2 = du_'8729''45'cong'691'_62 v2
du_'8729''45'cong'691'_62 ::
  T_Semilattice_10 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_62 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Lattice.Bundles.Semilattice._.∙-congˡ
d_'8729''45'cong'737'_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_64 ~v0 ~v1 v2 = du_'8729''45'cong'737'_64 v2
du_'8729''45'cong'737'_64 ::
  T_Semilattice_10 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_64 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Lattice.Bundles.Semilattice.band
d_band_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.T_Band_620
d_band_66 ~v0 ~v1 v2 = du_band_66 v2
du_band_66 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.T_Band_620
du_band_66 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_682
      (d__'8729'__28 (coe v0))
      (MAlonzo.Code.Algebra.Structures.d_isBand_620
         (coe d_isSemilattice_30 (coe v0)))
-- Algebra.Lattice.Bundles.Semilattice._._≉_
d__'8777'__70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> AgdaAny -> AgdaAny -> ()
d__'8777'__70 = erased
-- Algebra.Lattice.Bundles.Semilattice._.isBand
d_isBand_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_72 ~v0 ~v1 v2 = du_isBand_72 v2
du_isBand_72 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_72 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isBand_620
      (coe d_isSemilattice_30 (coe v0))
-- Algebra.Lattice.Bundles.Semilattice._.isMagma
d_isMagma_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_74 ~v0 ~v1 v2 = du_isMagma_74 v2
du_isMagma_74 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_74 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe
            MAlonzo.Code.Algebra.Structures.d_isBand_620
            (coe d_isSemilattice_30 (coe v0))))
-- Algebra.Lattice.Bundles.Semilattice._.isSemigroup
d_isSemigroup_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_76 ~v0 ~v1 v2 = du_isSemigroup_76 v2
du_isSemigroup_76 ::
  T_Semilattice_10 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_76 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
      (coe
         MAlonzo.Code.Algebra.Structures.d_isBand_620
         (coe d_isSemilattice_30 (coe v0)))
-- Algebra.Lattice.Bundles.Semilattice._.magma
d_magma_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_magma_78 ~v0 ~v1 v2 = du_magma_78 v2
du_magma_78 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.T_Magma_74
du_magma_78 v0
  = let v1 = coe du_band_66 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_magma_606
         (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_672 (coe v1)))
-- Algebra.Lattice.Bundles.Semilattice._.rawMagma
d_rawMagma_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_rawMagma_80 ~v0 ~v1 v2 = du_rawMagma_80 v2
du_rawMagma_80 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_rawMagma_80 v0
  = let v1 = coe du_band_66 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_672 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_rawMagma_118
            (coe MAlonzo.Code.Algebra.Bundles.du_magma_606 (coe v2))))
-- Algebra.Lattice.Bundles.Semilattice._.semigroup
d_semigroup_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_semigroup_82 ~v0 ~v1 v2 = du_semigroup_82 v2
du_semigroup_82 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_semigroup_82 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_semigroup_672
      (coe du_band_66 (coe v0))
-- Algebra.Lattice.Bundles.MeetSemilattice
d_MeetSemilattice_90 a0 a1 = ()
data T_MeetSemilattice_90
  = C_constructor_158 (AgdaAny -> AgdaAny -> AgdaAny)
                      MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
-- Algebra.Lattice.Bundles.MeetSemilattice.Carrier
d_Carrier_104 :: T_MeetSemilattice_90 -> ()
d_Carrier_104 = erased
-- Algebra.Lattice.Bundles.MeetSemilattice._≈_
d__'8776'__106 :: T_MeetSemilattice_90 -> AgdaAny -> AgdaAny -> ()
d__'8776'__106 = erased
-- Algebra.Lattice.Bundles.MeetSemilattice._∧_
d__'8743'__108 ::
  T_MeetSemilattice_90 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__108 v0
  = case coe v0 of
      C_constructor_158 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.MeetSemilattice.isMeetSemilattice
d_isMeetSemilattice_110 ::
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isMeetSemilattice_110 v0
  = case coe v0 of
      C_constructor_158 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.MeetSemilattice._.assoc
d_assoc_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_114 ~v0 ~v1 v2 = du_assoc_114 v2
du_assoc_114 ::
  T_MeetSemilattice_90 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_114 v0
  = let v1 = d_isMeetSemilattice_110 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.comm
d_comm_116 :: T_MeetSemilattice_90 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_116 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_622
      (coe d_isMeetSemilattice_110 (coe v0))
-- Algebra.Lattice.Bundles.MeetSemilattice._.idem
d_idem_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 -> AgdaAny -> AgdaAny
d_idem_118 ~v0 ~v1 v2 = du_idem_118 v2
du_idem_118 :: T_MeetSemilattice_90 -> AgdaAny -> AgdaAny
du_idem_118 v0
  = let v1 = d_isMeetSemilattice_110 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_idem_536
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))
-- Algebra.Lattice.Bundles.MeetSemilattice._.isBand
d_isBand_120 ::
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_120 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isBand_620
      (coe d_isMeetSemilattice_110 (coe v0))
-- Algebra.Lattice.Bundles.MeetSemilattice._.isEquivalence
d_isEquivalence_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_122 ~v0 ~v1 v2 = du_isEquivalence_122 v2
du_isEquivalence_122 ::
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_122 v0
  = let v1 = d_isMeetSemilattice_110 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.isMagma
d_isMagma_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_124 ~v0 ~v1 v2 = du_isMagma_124 v2
du_isMagma_124 ::
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_124 v0
  = let v1 = d_isMeetSemilattice_110 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.isPartialEquivalence
d_isPartialEquivalence_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_126 ~v0 ~v1 v2
  = du_isPartialEquivalence_126 v2
du_isPartialEquivalence_126 ::
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_126 v0
  = let v1 = d_isMeetSemilattice_110 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v4))))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.isSemigroup
d_isSemigroup_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_128 ~v0 ~v1 v2 = du_isSemigroup_128 v2
du_isSemigroup_128 ::
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_128 v0
  = let v1 = d_isMeetSemilattice_110 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))
-- Algebra.Lattice.Bundles.MeetSemilattice._.refl
d_refl_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 -> AgdaAny -> AgdaAny
d_refl_130 ~v0 ~v1 v2 = du_refl_130 v2
du_refl_130 :: T_MeetSemilattice_90 -> AgdaAny -> AgdaAny
du_refl_130 v0
  = let v1 = d_isMeetSemilattice_110 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.reflexive
d_reflexive_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_132 ~v0 ~v1 v2 = du_reflexive_132 v2
du_reflexive_132 ::
  T_MeetSemilattice_90 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_132 v0
  = let v1 = d_isMeetSemilattice_110 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v4))
                    v5))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.setoid
d_setoid_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_134 ~v0 ~v1 v2 = du_setoid_134 v2
du_setoid_134 ::
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_134 v0
  = let v1 = d_isMeetSemilattice_110 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_202
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3)))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.sym
d_sym_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_136 ~v0 ~v1 v2 = du_sym_136 v2
du_sym_136 ::
  T_MeetSemilattice_90 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_136 v0
  = let v1 = d_isMeetSemilattice_110 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.trans
d_trans_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_138 ~v0 ~v1 v2 = du_trans_138 v2
du_trans_138 ::
  T_MeetSemilattice_90 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_138 v0
  = let v1 = d_isMeetSemilattice_110 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.∙-cong
d_'8729''45'cong_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_140 ~v0 ~v1 v2 = du_'8729''45'cong_140 v2
du_'8729''45'cong_140 ::
  T_MeetSemilattice_90 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_140 v0
  = let v1 = d_isMeetSemilattice_110 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.∙-congʳ
d_'8729''45'cong'691'_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_142 ~v0 ~v1 v2
  = du_'8729''45'cong'691'_142 v2
du_'8729''45'cong'691'_142 ::
  T_MeetSemilattice_90 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_142 v0
  = let v1 = d_isMeetSemilattice_110 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.∙-congˡ
d_'8729''45'cong'737'_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_144 ~v0 ~v1 v2
  = du_'8729''45'cong'737'_144 v2
du_'8729''45'cong'737'_144 ::
  T_MeetSemilattice_90 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_144 v0
  = let v1 = d_isMeetSemilattice_110 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Lattice.Bundles.MeetSemilattice.semilattice
d_semilattice_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 -> T_Semilattice_10
d_semilattice_146 ~v0 ~v1 v2 = du_semilattice_146 v2
du_semilattice_146 :: T_MeetSemilattice_90 -> T_Semilattice_10
du_semilattice_146 v0
  = coe
      C_constructor_84 (d__'8743'__108 (coe v0))
      (d_isMeetSemilattice_110 (coe v0))
-- Algebra.Lattice.Bundles.MeetSemilattice._.band
d_band_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 -> MAlonzo.Code.Algebra.Bundles.T_Band_620
d_band_150 ~v0 ~v1 v2 = du_band_150 v2
du_band_150 ::
  T_MeetSemilattice_90 -> MAlonzo.Code.Algebra.Bundles.T_Band_620
du_band_150 v0 = coe du_band_66 (coe du_semilattice_146 (coe v0))
-- Algebra.Lattice.Bundles.MeetSemilattice._.magma
d_magma_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 -> MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_magma_152 ~v0 ~v1 v2 = du_magma_152 v2
du_magma_152 ::
  T_MeetSemilattice_90 -> MAlonzo.Code.Algebra.Bundles.T_Magma_74
du_magma_152 v0
  = let v1 = coe du_semilattice_146 (coe v0) in
    coe
      (let v2 = coe du_band_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_magma_606
            (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_672 (coe v2))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.rawMagma
d_rawMagma_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_rawMagma_154 ~v0 ~v1 v2 = du_rawMagma_154 v2
du_rawMagma_154 ::
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_rawMagma_154 v0
  = let v1 = coe du_semilattice_146 (coe v0) in
    coe
      (let v2 = coe du_band_66 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_672 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_rawMagma_118
               (coe MAlonzo.Code.Algebra.Bundles.du_magma_606 (coe v3)))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.semigroup
d_semigroup_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_semigroup_156 ~v0 ~v1 v2 = du_semigroup_156 v2
du_semigroup_156 ::
  T_MeetSemilattice_90 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_semigroup_156 v0
  = let v1 = coe du_semilattice_146 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_semigroup_672
         (coe du_band_66 (coe v1)))
-- Algebra.Lattice.Bundles.JoinSemilattice
d_JoinSemilattice_164 a0 a1 = ()
data T_JoinSemilattice_164
  = C_constructor_232 (AgdaAny -> AgdaAny -> AgdaAny)
                      MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
-- Algebra.Lattice.Bundles.JoinSemilattice.Carrier
d_Carrier_178 :: T_JoinSemilattice_164 -> ()
d_Carrier_178 = erased
-- Algebra.Lattice.Bundles.JoinSemilattice._≈_
d__'8776'__180 :: T_JoinSemilattice_164 -> AgdaAny -> AgdaAny -> ()
d__'8776'__180 = erased
-- Algebra.Lattice.Bundles.JoinSemilattice._∨_
d__'8744'__182 ::
  T_JoinSemilattice_164 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__182 v0
  = case coe v0 of
      C_constructor_232 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.JoinSemilattice.isJoinSemilattice
d_isJoinSemilattice_184 ::
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isJoinSemilattice_184 v0
  = case coe v0 of
      C_constructor_232 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.JoinSemilattice._.assoc
d_assoc_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_188 ~v0 ~v1 v2 = du_assoc_188 v2
du_assoc_188 ::
  T_JoinSemilattice_164 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_188 v0
  = let v1 = d_isJoinSemilattice_184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.comm
d_comm_190 ::
  T_JoinSemilattice_164 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_190 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_622
      (coe d_isJoinSemilattice_184 (coe v0))
-- Algebra.Lattice.Bundles.JoinSemilattice._.idem
d_idem_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 -> AgdaAny -> AgdaAny
d_idem_192 ~v0 ~v1 v2 = du_idem_192 v2
du_idem_192 :: T_JoinSemilattice_164 -> AgdaAny -> AgdaAny
du_idem_192 v0
  = let v1 = d_isJoinSemilattice_184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_idem_536
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))
-- Algebra.Lattice.Bundles.JoinSemilattice._.isBand
d_isBand_194 ::
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_194 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isBand_620
      (coe d_isJoinSemilattice_184 (coe v0))
-- Algebra.Lattice.Bundles.JoinSemilattice._.isEquivalence
d_isEquivalence_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_196 ~v0 ~v1 v2 = du_isEquivalence_196 v2
du_isEquivalence_196 ::
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_196 v0
  = let v1 = d_isJoinSemilattice_184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.isMagma
d_isMagma_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_198 ~v0 ~v1 v2 = du_isMagma_198 v2
du_isMagma_198 ::
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_198 v0
  = let v1 = d_isJoinSemilattice_184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.isPartialEquivalence
d_isPartialEquivalence_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_200 ~v0 ~v1 v2
  = du_isPartialEquivalence_200 v2
du_isPartialEquivalence_200 ::
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_200 v0
  = let v1 = d_isJoinSemilattice_184 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v4))))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.isSemigroup
d_isSemigroup_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_202 ~v0 ~v1 v2 = du_isSemigroup_202 v2
du_isSemigroup_202 ::
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_202 v0
  = let v1 = d_isJoinSemilattice_184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))
-- Algebra.Lattice.Bundles.JoinSemilattice._.refl
d_refl_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 -> AgdaAny -> AgdaAny
d_refl_204 ~v0 ~v1 v2 = du_refl_204 v2
du_refl_204 :: T_JoinSemilattice_164 -> AgdaAny -> AgdaAny
du_refl_204 v0
  = let v1 = d_isJoinSemilattice_184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.reflexive
d_reflexive_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_206 ~v0 ~v1 v2 = du_reflexive_206 v2
du_reflexive_206 ::
  T_JoinSemilattice_164 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_206 v0
  = let v1 = d_isJoinSemilattice_184 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                    (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v4))
                    v5))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.setoid
d_setoid_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_208 ~v0 ~v1 v2 = du_setoid_208 v2
du_setoid_208 ::
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_208 v0
  = let v1 = d_isJoinSemilattice_184 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_202
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3)))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.sym
d_sym_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_210 ~v0 ~v1 v2 = du_sym_210 v2
du_sym_210 ::
  T_JoinSemilattice_164 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_210 v0
  = let v1 = d_isJoinSemilattice_184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.trans
d_trans_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_212 ~v0 ~v1 v2 = du_trans_212 v2
du_trans_212 ::
  T_JoinSemilattice_164 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_212 v0
  = let v1 = d_isJoinSemilattice_184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1))))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.∙-cong
d_'8729''45'cong_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_214 ~v0 ~v1 v2 = du_'8729''45'cong_214 v2
du_'8729''45'cong_214 ::
  T_JoinSemilattice_164 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_214 v0
  = let v1 = d_isJoinSemilattice_184 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1)))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.∙-congʳ
d_'8729''45'cong'691'_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_216 ~v0 ~v1 v2
  = du_'8729''45'cong'691'_216 v2
du_'8729''45'cong'691'_216 ::
  T_JoinSemilattice_164 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_216 v0
  = let v1 = d_isJoinSemilattice_184 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.∙-congˡ
d_'8729''45'cong'737'_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_218 ~v0 ~v1 v2
  = du_'8729''45'cong'737'_218 v2
du_'8729''45'cong'737'_218 ::
  T_JoinSemilattice_164 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_218 v0
  = let v1 = d_isJoinSemilattice_184 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v6)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                              (coe v5)))))))))
-- Algebra.Lattice.Bundles.JoinSemilattice.semilattice
d_semilattice_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 -> T_Semilattice_10
d_semilattice_220 ~v0 ~v1 v2 = du_semilattice_220 v2
du_semilattice_220 :: T_JoinSemilattice_164 -> T_Semilattice_10
du_semilattice_220 v0
  = coe
      C_constructor_84 (d__'8744'__182 (coe v0))
      (d_isJoinSemilattice_184 (coe v0))
-- Algebra.Lattice.Bundles.JoinSemilattice._.band
d_band_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 -> MAlonzo.Code.Algebra.Bundles.T_Band_620
d_band_224 ~v0 ~v1 v2 = du_band_224 v2
du_band_224 ::
  T_JoinSemilattice_164 -> MAlonzo.Code.Algebra.Bundles.T_Band_620
du_band_224 v0 = coe du_band_66 (coe du_semilattice_220 (coe v0))
-- Algebra.Lattice.Bundles.JoinSemilattice._.magma
d_magma_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 -> MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_magma_226 ~v0 ~v1 v2 = du_magma_226 v2
du_magma_226 ::
  T_JoinSemilattice_164 -> MAlonzo.Code.Algebra.Bundles.T_Magma_74
du_magma_226 v0
  = let v1 = coe du_semilattice_220 (coe v0) in
    coe
      (let v2 = coe du_band_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_magma_606
            (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_672 (coe v2))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.rawMagma
d_rawMagma_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_rawMagma_228 ~v0 ~v1 v2 = du_rawMagma_228 v2
du_rawMagma_228 ::
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_rawMagma_228 v0
  = let v1 = coe du_semilattice_220 (coe v0) in
    coe
      (let v2 = coe du_band_66 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_672 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_rawMagma_118
               (coe MAlonzo.Code.Algebra.Bundles.du_magma_606 (coe v3)))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.semigroup
d_semigroup_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_semigroup_230 ~v0 ~v1 v2 = du_semigroup_230 v2
du_semigroup_230 ::
  T_JoinSemilattice_164 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_semigroup_230 v0
  = let v1 = coe du_semilattice_220 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_semigroup_672
         (coe du_band_66 (coe v1)))
-- Algebra.Lattice.Bundles.BoundedSemilattice
d_BoundedSemilattice_238 a0 a1 = ()
data T_BoundedSemilattice_238
  = C_constructor_330 (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny
                      MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
-- Algebra.Lattice.Bundles.BoundedSemilattice.Carrier
d_Carrier_254 :: T_BoundedSemilattice_238 -> ()
d_Carrier_254 = erased
-- Algebra.Lattice.Bundles.BoundedSemilattice._≈_
d__'8776'__256 ::
  T_BoundedSemilattice_238 -> AgdaAny -> AgdaAny -> ()
d__'8776'__256 = erased
-- Algebra.Lattice.Bundles.BoundedSemilattice._∙_
d__'8729'__258 ::
  T_BoundedSemilattice_238 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__258 v0
  = case coe v0 of
      C_constructor_330 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedSemilattice.ε
d_ε_260 :: T_BoundedSemilattice_238 -> AgdaAny
d_ε_260 v0
  = case coe v0 of
      C_constructor_330 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedSemilattice.isBoundedSemilattice
d_isBoundedSemilattice_262 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
d_isBoundedSemilattice_262 v0
  = case coe v0 of
      C_constructor_330 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedSemilattice._.assoc
d_assoc_266 ::
  T_BoundedSemilattice_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_266 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_498
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
               (coe d_isBoundedSemilattice_262 (coe v0)))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.comm
d_comm_268 ::
  T_BoundedSemilattice_238 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_268 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_776
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
         (coe d_isBoundedSemilattice_262 (coe v0)))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.idem
d_idem_270 :: T_BoundedSemilattice_238 -> AgdaAny -> AgdaAny
d_idem_270 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_idem_896
      (coe d_isBoundedSemilattice_262 (coe v0))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.identity
d_identity_272 ::
  T_BoundedSemilattice_238 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_272 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe d_isBoundedSemilattice_262 (coe v0))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.identityʳ
d_identity'691'_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 -> AgdaAny -> AgdaAny
d_identity'691'_274 ~v0 ~v1 v2 = du_identity'691'_274 v2
du_identity'691'_274 ::
  T_BoundedSemilattice_238 -> AgdaAny -> AgdaAny
du_identity'691'_274 v0
  = let v1 = d_isBoundedSemilattice_262 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'691'_754
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.identityˡ
d_identity'737'_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 -> AgdaAny -> AgdaAny
d_identity'737'_276 ~v0 ~v1 v2 = du_identity'737'_276 v2
du_identity'737'_276 ::
  T_BoundedSemilattice_238 -> AgdaAny -> AgdaAny
du_identity'737'_276 v0
  = let v1 = d_isBoundedSemilattice_262 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'737'_752
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isBand
d_isBand_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_278 ~v0 ~v1 v2 = du_isBand_278 v2
du_isBand_278 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_278 v0
  = let v1 = d_isBoundedSemilattice_262 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isBand_876
         (coe
            MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942
            (coe v1)))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isCommutativeMagma
d_isCommutativeMagma_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
d_isCommutativeMagma_280 ~v0 ~v1 v2 = du_isCommutativeMagma_280 v2
du_isCommutativeMagma_280 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_214
du_isCommutativeMagma_280 v0
  = let v1 = d_isBoundedSemilattice_262 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_606
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
               (coe v2))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isCommutativeMonoid
d_isCommutativeMonoid_282 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_764
d_isCommutativeMonoid_282 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
      (coe d_isBoundedSemilattice_262 (coe v0))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isCommutativeSemigroup
d_isCommutativeSemigroup_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_isCommutativeSemigroup_284 ~v0 ~v1 v2
  = du_isCommutativeSemigroup_284 v2
du_isCommutativeSemigroup_284 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_isCommutativeSemigroup_284 v0
  = let v1 = d_isBoundedSemilattice_262 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_814
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v1)))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isEquivalence
d_isEquivalence_286 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_286 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_774
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                  (coe d_isBoundedSemilattice_262 (coe v0))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isIdempotentMonoid
d_isIdempotentMonoid_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
d_isIdempotentMonoid_288 ~v0 ~v1 v2 = du_isIdempotentMonoid_288 v2
du_isIdempotentMonoid_288 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_826
du_isIdempotentMonoid_288 v0
  = let v1 = d_isBoundedSemilattice_262 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942 (coe v1))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isMagma
d_isMagma_290 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_290 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_496
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_774
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
               (coe d_isBoundedSemilattice_262 (coe v0)))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isMonoid
d_isMonoid_292 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_isMonoid_292 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_774
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
         (coe d_isBoundedSemilattice_262 (coe v0)))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isPartialEquivalence
d_isPartialEquivalence_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_294 ~v0 ~v1 v2
  = du_isPartialEquivalence_294 v2
du_isPartialEquivalence_294 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_294 v0
  = let v1 = d_isBoundedSemilattice_262 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v5)))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isSemigroup
d_isSemigroup_296 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_296 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe d_isBoundedSemilattice_262 (coe v0))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isCommutativeBand
d_isCommutativeBand_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_298 ~v0 ~v1 v2 = du_isCommutativeBand_298 v2
du_isCommutativeBand_298 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_298 v0
  = let v1 = d_isBoundedSemilattice_262 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948 (coe v1))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isUnitalMagma
d_isUnitalMagma_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
d_isUnitalMagma_300 ~v0 ~v1 v2 = du_isUnitalMagma_300 v2
du_isUnitalMagma_300 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_666
du_isUnitalMagma_300 v0
  = let v1 = d_isBoundedSemilattice_262 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_756
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.refl
d_refl_302 :: T_BoundedSemilattice_238 -> AgdaAny -> AgdaAny
d_refl_302 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                     (coe d_isBoundedSemilattice_262 (coe v0)))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.reflexive
d_reflexive_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_304 ~v0 ~v1 v2 = du_reflexive_304 v2
du_reflexive_304 ::
  T_BoundedSemilattice_238 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_304 v0
  = let v1 = d_isBoundedSemilattice_262 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                       (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v5))
                       v6)))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.setoid
d_setoid_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_306 ~v0 ~v1 v2 = du_setoid_306 v2
du_setoid_306 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_306 v0
  = let v1 = d_isBoundedSemilattice_262 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_202
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.sym
d_sym_308 ::
  T_BoundedSemilattice_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_308 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                     (coe d_isBoundedSemilattice_262 (coe v0)))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.trans
d_trans_310 ::
  T_BoundedSemilattice_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_310 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_774
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                     (coe d_isBoundedSemilattice_262 (coe v0)))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.∙-cong
d_'8729''45'cong_312 ::
  T_BoundedSemilattice_238 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_312 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_496
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_722
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_774
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                  (coe d_isBoundedSemilattice_262 (coe v0))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.∙-congʳ
d_'8729''45'cong'691'_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_314 ~v0 ~v1 v2
  = du_'8729''45'cong'691'_314 v2
du_'8729''45'cong'691'_314 ::
  T_BoundedSemilattice_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_314 v0
  = let v1 = d_isBoundedSemilattice_262 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (let v6
                         = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.∙-congˡ
d_'8729''45'cong'737'_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_316 ~v0 ~v1 v2
  = du_'8729''45'cong'737'_316 v2
du_'8729''45'cong'737'_316 ::
  T_BoundedSemilattice_238 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_316 v0
  = let v1 = d_isBoundedSemilattice_262 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (let v6
                         = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice.semilattice
d_semilattice_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 -> T_Semilattice_10
d_semilattice_318 ~v0 ~v1 v2 = du_semilattice_318 v2
du_semilattice_318 :: T_BoundedSemilattice_238 -> T_Semilattice_10
du_semilattice_318 v0
  = coe
      C_constructor_84 (d__'8729'__258 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
         (coe d_isBoundedSemilattice_262 (coe v0)))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.band
d_band_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 -> MAlonzo.Code.Algebra.Bundles.T_Band_620
d_band_322 ~v0 ~v1 v2 = du_band_322 v2
du_band_322 ::
  T_BoundedSemilattice_238 -> MAlonzo.Code.Algebra.Bundles.T_Band_620
du_band_322 v0 = coe du_band_66 (coe du_semilattice_318 (coe v0))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.magma
d_magma_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 -> MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_magma_324 ~v0 ~v1 v2 = du_magma_324 v2
du_magma_324 ::
  T_BoundedSemilattice_238 -> MAlonzo.Code.Algebra.Bundles.T_Magma_74
du_magma_324 v0
  = let v1 = coe du_semilattice_318 (coe v0) in
    coe
      (let v2 = coe du_band_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_magma_606
            (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_672 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.rawMagma
d_rawMagma_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_rawMagma_326 ~v0 ~v1 v2 = du_rawMagma_326 v2
du_rawMagma_326 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_rawMagma_326 v0
  = let v1 = coe du_semilattice_318 (coe v0) in
    coe
      (let v2 = coe du_band_66 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_672 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_rawMagma_118
               (coe MAlonzo.Code.Algebra.Bundles.du_magma_606 (coe v3)))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.semigroup
d_semigroup_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_semigroup_328 ~v0 ~v1 v2 = du_semigroup_328 v2
du_semigroup_328 ::
  T_BoundedSemilattice_238 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_semigroup_328 v0
  = let v1 = coe du_semilattice_318 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_semigroup_672
         (coe du_band_66 (coe v1)))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice
d_BoundedMeetSemilattice_336 a0 a1 = ()
data T_BoundedMeetSemilattice_336
  = C_constructor_418 (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny
                      MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice.Carrier
d_Carrier_352 :: T_BoundedMeetSemilattice_336 -> ()
d_Carrier_352 = erased
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._≈_
d__'8776'__354 ::
  T_BoundedMeetSemilattice_336 -> AgdaAny -> AgdaAny -> ()
d__'8776'__354 = erased
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._∧_
d__'8743'__356 ::
  T_BoundedMeetSemilattice_336 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__356 v0
  = case coe v0 of
      C_constructor_418 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice.⊤
d_'8868'_358 :: T_BoundedMeetSemilattice_336 -> AgdaAny
d_'8868'_358 v0
  = case coe v0 of
      C_constructor_418 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_360 ::
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
d_isBoundedMeetSemilattice_360 v0
  = case coe v0 of
      C_constructor_418 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.assoc
d_assoc_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_364 ~v0 ~v1 v2 = du_assoc_364 v2
du_assoc_364 ::
  T_BoundedMeetSemilattice_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_364 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_498
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2)))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.comm
d_comm_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_366 ~v0 ~v1 v2 = du_comm_366 v2
du_comm_366 ::
  T_BoundedMeetSemilattice_336 -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_366 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_comm_776
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v1)))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.idem
d_idem_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 -> AgdaAny -> AgdaAny
d_idem_368 ~v0 ~v1 v2 = du_idem_368 v2
du_idem_368 :: T_BoundedMeetSemilattice_336 -> AgdaAny -> AgdaAny
du_idem_368 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_idem_536
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.identity
d_identity_370 ::
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_370 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe d_isBoundedMeetSemilattice_360 (coe v0))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.identityʳ
d_identity'691'_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 -> AgdaAny -> AgdaAny
d_identity'691'_372 ~v0 ~v1 v2 = du_identity'691'_372 v2
du_identity'691'_372 ::
  T_BoundedMeetSemilattice_336 -> AgdaAny -> AgdaAny
du_identity'691'_372 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'691'_754
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.identityˡ
d_identity'737'_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 -> AgdaAny -> AgdaAny
d_identity'737'_374 ~v0 ~v1 v2 = du_identity'737'_374 v2
du_identity'737'_374 ::
  T_BoundedMeetSemilattice_336 -> AgdaAny -> AgdaAny
du_identity'737'_374 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'737'_752
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.isBand
d_isBand_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_376 ~v0 ~v1 v2 = du_isBand_376 v2
du_isBand_376 ::
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_376 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isBand_876
         (coe
            MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942
            (coe v1)))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.isEquivalence
d_isEquivalence_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_378 ~v0 ~v1 v2 = du_isEquivalence_378 v2
du_isEquivalence_378 ::
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_378 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.isMagma
d_isMagma_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_380 ~v0 ~v1 v2 = du_isMagma_380 v2
du_isMagma_380 ::
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_380 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2)))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.isCommutativeBand
d_isCommutativeBand_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_382 ~v0 ~v1 v2 = du_isCommutativeBand_382 v2
du_isCommutativeBand_382 ::
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_382 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948 (coe v1))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.isPartialEquivalence
d_isPartialEquivalence_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_384 ~v0 ~v1 v2
  = du_isPartialEquivalence_384 v2
du_isPartialEquivalence_384 ::
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_384 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v5)))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.isSemigroup
d_isSemigroup_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_386 ~v0 ~v1 v2 = du_isSemigroup_386 v2
du_isSemigroup_386 ::
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_386 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.refl
d_refl_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 -> AgdaAny -> AgdaAny
d_refl_388 ~v0 ~v1 v2 = du_refl_388 v2
du_refl_388 :: T_BoundedMeetSemilattice_336 -> AgdaAny -> AgdaAny
du_refl_388 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                     (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2)))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.reflexive
d_reflexive_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_390 ~v0 ~v1 v2 = du_reflexive_390 v2
du_reflexive_390 ::
  T_BoundedMeetSemilattice_336 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_390 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                       (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v5))
                       v6)))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.setoid
d_setoid_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_392 ~v0 ~v1 v2 = du_setoid_392 v2
du_setoid_392 ::
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_392 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_202
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.sym
d_sym_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_394 ~v0 ~v1 v2 = du_sym_394 v2
du_sym_394 ::
  T_BoundedMeetSemilattice_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_394 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                     (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2)))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.trans
d_trans_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_396 ~v0 ~v1 v2 = du_trans_396 v2
du_trans_396 ::
  T_BoundedMeetSemilattice_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_396 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                     (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2)))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.∙-cong
d_'8729''45'cong_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_398 ~v0 ~v1 v2 = du_'8729''45'cong_398 v2
du_'8729''45'cong_398 ::
  T_BoundedMeetSemilattice_336 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_398 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.∙-congʳ
d_'8729''45'cong'691'_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_400 ~v0 ~v1 v2
  = du_'8729''45'cong'691'_400 v2
du_'8729''45'cong'691'_400 ::
  T_BoundedMeetSemilattice_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_400 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (let v6
                         = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.∙-congˡ
d_'8729''45'cong'737'_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_402 ~v0 ~v1 v2
  = du_'8729''45'cong'737'_402 v2
du_'8729''45'cong'737'_402 ::
  T_BoundedMeetSemilattice_336 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_402 v0
  = let v1 = d_isBoundedMeetSemilattice_360 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (let v6
                         = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice.boundedSemilattice
d_boundedSemilattice_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 -> T_BoundedSemilattice_238
d_boundedSemilattice_404 ~v0 ~v1 v2 = du_boundedSemilattice_404 v2
du_boundedSemilattice_404 ::
  T_BoundedMeetSemilattice_336 -> T_BoundedSemilattice_238
du_boundedSemilattice_404 v0
  = coe
      C_constructor_330 (d__'8743'__356 (coe v0)) (d_'8868'_358 (coe v0))
      (d_isBoundedMeetSemilattice_360 (coe v0))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.band
d_band_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_620
d_band_408 ~v0 ~v1 v2 = du_band_408 v2
du_band_408 ::
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_620
du_band_408 v0
  = let v1 = coe du_boundedSemilattice_404 (coe v0) in
    coe (coe du_band_66 (coe du_semilattice_318 (coe v1)))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.magma
d_magma_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_magma_410 ~v0 ~v1 v2 = du_magma_410 v2
du_magma_410 ::
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_74
du_magma_410 v0
  = let v1 = coe du_boundedSemilattice_404 (coe v0) in
    coe
      (let v2 = coe du_semilattice_318 (coe v1) in
       coe
         (let v3 = coe du_band_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_magma_606
               (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_672 (coe v3)))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.rawMagma
d_rawMagma_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_rawMagma_412 ~v0 ~v1 v2 = du_rawMagma_412 v2
du_rawMagma_412 ::
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_rawMagma_412 v0
  = let v1 = coe du_boundedSemilattice_404 (coe v0) in
    coe
      (let v2 = coe du_semilattice_318 (coe v1) in
       coe
         (let v3 = coe du_band_66 (coe v2) in
          coe
            (let v4
                   = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_672 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_rawMagma_118
                  (coe MAlonzo.Code.Algebra.Bundles.du_magma_606 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.semigroup
d_semigroup_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_semigroup_414 ~v0 ~v1 v2 = du_semigroup_414 v2
du_semigroup_414 ::
  T_BoundedMeetSemilattice_336 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_semigroup_414 v0
  = let v1 = coe du_boundedSemilattice_404 (coe v0) in
    coe
      (let v2 = coe du_semilattice_318 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_semigroup_672
            (coe du_band_66 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.semilattice
d_semilattice_416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_336 -> T_Semilattice_10
d_semilattice_416 ~v0 ~v1 v2 = du_semilattice_416 v2
du_semilattice_416 ::
  T_BoundedMeetSemilattice_336 -> T_Semilattice_10
du_semilattice_416 v0
  = coe du_semilattice_318 (coe du_boundedSemilattice_404 (coe v0))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice
d_BoundedJoinSemilattice_424 a0 a1 = ()
data T_BoundedJoinSemilattice_424
  = C_constructor_506 (AgdaAny -> AgdaAny -> AgdaAny) AgdaAny
                      MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice.Carrier
d_Carrier_440 :: T_BoundedJoinSemilattice_424 -> ()
d_Carrier_440 = erased
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._≈_
d__'8776'__442 ::
  T_BoundedJoinSemilattice_424 -> AgdaAny -> AgdaAny -> ()
d__'8776'__442 = erased
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._∨_
d__'8744'__444 ::
  T_BoundedJoinSemilattice_424 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__444 v0
  = case coe v0 of
      C_constructor_506 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice.⊥
d_'8869'_446 :: T_BoundedJoinSemilattice_424 -> AgdaAny
d_'8869'_446 v0
  = case coe v0 of
      C_constructor_506 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_448 ::
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_884
d_isBoundedJoinSemilattice_448 v0
  = case coe v0 of
      C_constructor_506 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.assoc
d_assoc_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_452 ~v0 ~v1 v2 = du_assoc_452 v2
du_assoc_452 ::
  T_BoundedJoinSemilattice_424 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_452 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_498
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2)))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.comm
d_comm_454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_454 ~v0 ~v1 v2 = du_comm_454 v2
du_comm_454 ::
  T_BoundedJoinSemilattice_424 -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_454 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_comm_776
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe v1)))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.idem
d_idem_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 -> AgdaAny -> AgdaAny
d_idem_456 ~v0 ~v1 v2 = du_idem_456 v2
du_idem_456 :: T_BoundedJoinSemilattice_424 -> AgdaAny -> AgdaAny
du_idem_456 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_idem_536
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.identity
d_identity_458 ::
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_458 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_724
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_774
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
            (coe d_isBoundedJoinSemilattice_448 (coe v0))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.identityʳ
d_identity'691'_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 -> AgdaAny -> AgdaAny
d_identity'691'_460 ~v0 ~v1 v2 = du_identity'691'_460 v2
du_identity'691'_460 ::
  T_BoundedJoinSemilattice_424 -> AgdaAny -> AgdaAny
du_identity'691'_460 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'691'_754
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.identityˡ
d_identity'737'_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 -> AgdaAny -> AgdaAny
d_identity'737'_462 ~v0 ~v1 v2 = du_identity'737'_462 v2
du_identity'737'_462 ::
  T_BoundedJoinSemilattice_424 -> AgdaAny -> AgdaAny
du_identity'737'_462 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_894
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'737'_752
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_774 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.isBand
d_isBand_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_464 ~v0 ~v1 v2 = du_isBand_464 v2
du_isBand_464 ::
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_464 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isBand_876
         (coe
            MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_942
            (coe v1)))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.isEquivalence
d_isEquivalence_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_466 ~v0 ~v1 v2 = du_isEquivalence_466 v2
du_isEquivalence_466 ::
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_466 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.isCommutativeBand
d_isCommutativeBand_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_isCommutativeBand_468 ~v0 ~v1 v2 = du_isCommutativeBand_468 v2
du_isCommutativeBand_468 ::
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_isCommutativeBand_468 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948 (coe v1))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.isMagma
d_isMagma_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_470 ~v0 ~v1 v2 = du_isMagma_470 v2
du_isMagma_470 ::
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_470 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2)))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.isPartialEquivalence
d_isPartialEquivalence_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_472 ~v0 ~v1 v2
  = du_isPartialEquivalence_472 v2
du_isPartialEquivalence_472 ::
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_472 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v5)))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.isSemigroup
d_isSemigroup_474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_474 ~v0 ~v1 v2 = du_isSemigroup_474 v2
du_isSemigroup_474 ::
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_474 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.refl
d_refl_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 -> AgdaAny -> AgdaAny
d_refl_476 ~v0 ~v1 v2 = du_refl_476 v2
du_refl_476 :: T_BoundedJoinSemilattice_424 -> AgdaAny -> AgdaAny
du_refl_476 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                     (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2)))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.reflexive
d_reflexive_478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_478 ~v0 ~v1 v2 = du_reflexive_478 v2
du_reflexive_478 ::
  T_BoundedJoinSemilattice_424 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_478 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                       (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v5))
                       v6)))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.setoid
d_setoid_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_480 ~v0 ~v1 v2 = du_setoid_480 v2
du_setoid_480 ::
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_480 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_202
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.sym
d_sym_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_482 ~v0 ~v1 v2 = du_sym_482 v2
du_sym_482 ::
  T_BoundedJoinSemilattice_424 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_482 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                     (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2)))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.trans
d_trans_484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_484 ~v0 ~v1 v2 = du_trans_484 v2
du_trans_484 ::
  T_BoundedJoinSemilattice_424 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_484 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                     (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2)))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.∙-cong
d_'8729''45'cong_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_486 ~v0 ~v1 v2 = du_'8729''45'cong_486 v2
du_'8729''45'cong_486 ::
  T_BoundedJoinSemilattice_424 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_486 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_534
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.∙-congʳ
d_'8729''45'cong'691'_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_488 ~v0 ~v1 v2
  = du_'8729''45'cong'691'_488 v2
du_'8729''45'cong'691'_488 ::
  T_BoundedJoinSemilattice_424 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_488 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (let v6
                         = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.∙-congˡ
d_'8729''45'cong'737'_490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_490 ~v0 ~v1 v2
  = du_'8729''45'cong'737'_490 v2
du_'8729''45'cong'737'_490 ::
  T_BoundedJoinSemilattice_424 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_490 v0
  = let v1 = d_isBoundedJoinSemilattice_448 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_948
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_620 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v4) in
                coe
                  (let v6
                         = coe MAlonzo.Code.Algebra.Structures.du_setoid_202 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v5) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                           (coe v7)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
                                 (coe v6))))))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice.boundedSemilattice
d_boundedSemilattice_492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 -> T_BoundedSemilattice_238
d_boundedSemilattice_492 ~v0 ~v1 v2 = du_boundedSemilattice_492 v2
du_boundedSemilattice_492 ::
  T_BoundedJoinSemilattice_424 -> T_BoundedSemilattice_238
du_boundedSemilattice_492 v0
  = coe
      C_constructor_330 (d__'8744'__444 (coe v0)) (d_'8869'_446 (coe v0))
      (d_isBoundedJoinSemilattice_448 (coe v0))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.band
d_band_496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_620
d_band_496 ~v0 ~v1 v2 = du_band_496 v2
du_band_496 ::
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_620
du_band_496 v0
  = let v1 = coe du_boundedSemilattice_492 (coe v0) in
    coe (coe du_band_66 (coe du_semilattice_318 (coe v1)))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.magma
d_magma_498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_magma_498 ~v0 ~v1 v2 = du_magma_498 v2
du_magma_498 ::
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_74
du_magma_498 v0
  = let v1 = coe du_boundedSemilattice_492 (coe v0) in
    coe
      (let v2 = coe du_semilattice_318 (coe v1) in
       coe
         (let v3 = coe du_band_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_magma_606
               (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_672 (coe v3)))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.rawMagma
d_rawMagma_500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_rawMagma_500 ~v0 ~v1 v2 = du_rawMagma_500 v2
du_rawMagma_500 ::
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_rawMagma_500 v0
  = let v1 = coe du_boundedSemilattice_492 (coe v0) in
    coe
      (let v2 = coe du_semilattice_318 (coe v1) in
       coe
         (let v3 = coe du_band_66 (coe v2) in
          coe
            (let v4
                   = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_672 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_rawMagma_118
                  (coe MAlonzo.Code.Algebra.Bundles.du_magma_606 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.semigroup
d_semigroup_502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_semigroup_502 ~v0 ~v1 v2 = du_semigroup_502 v2
du_semigroup_502 ::
  T_BoundedJoinSemilattice_424 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_semigroup_502 v0
  = let v1 = coe du_boundedSemilattice_492 (coe v0) in
    coe
      (let v2 = coe du_semilattice_318 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_semigroup_672
            (coe du_band_66 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.semilattice
d_semilattice_504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_424 -> T_Semilattice_10
d_semilattice_504 ~v0 ~v1 v2 = du_semilattice_504 v2
du_semilattice_504 ::
  T_BoundedJoinSemilattice_424 -> T_Semilattice_10
du_semilattice_504 v0
  = coe du_semilattice_318 (coe du_boundedSemilattice_492 (coe v0))
-- Algebra.Lattice.Bundles.Lattice
d_Lattice_512 a0 a1 = ()
data T_Lattice_512
  = C_constructor_592 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny)
                      MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
-- Algebra.Lattice.Bundles.Lattice.Carrier
d_Carrier_528 :: T_Lattice_512 -> ()
d_Carrier_528 = erased
-- Algebra.Lattice.Bundles.Lattice._≈_
d__'8776'__530 :: T_Lattice_512 -> AgdaAny -> AgdaAny -> ()
d__'8776'__530 = erased
-- Algebra.Lattice.Bundles.Lattice._∨_
d__'8744'__532 :: T_Lattice_512 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__532 v0
  = case coe v0 of
      C_constructor_592 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.Lattice._∧_
d__'8743'__534 :: T_Lattice_512 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__534 v0
  = case coe v0 of
      C_constructor_592 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.Lattice.isLattice
d_isLattice_536 ::
  T_Lattice_512 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_isLattice_536 v0
  = case coe v0 of
      C_constructor_592 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.Lattice._.absorptive
d_absorptive_540 ::
  T_Lattice_512 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_540 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3106
      (coe d_isLattice_536 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.isEquivalence
d_isEquivalence_542 ::
  T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_542 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
      (coe d_isLattice_536 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.isPartialEquivalence
d_isPartialEquivalence_544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_544 ~v0 ~v1 v2
  = du_isPartialEquivalence_544 v2
du_isPartialEquivalence_544 ::
  T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_544 v0
  = let v1 = d_isLattice_536 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
            (coe v1)))
-- Algebra.Lattice.Bundles.Lattice._.refl
d_refl_546 :: T_Lattice_512 -> AgdaAny -> AgdaAny
d_refl_546 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe d_isLattice_536 (coe v0)))
-- Algebra.Lattice.Bundles.Lattice._.reflexive
d_reflexive_548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_512 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_548 ~v0 ~v1 v2 = du_reflexive_548 v2
du_reflexive_548 ::
  T_Lattice_512 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_548 v0
  = let v1 = d_isLattice_536 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe
              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
              (coe v1))
           v2)
-- Algebra.Lattice.Bundles.Lattice._.sym
d_sym_550 ::
  T_Lattice_512 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_550 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe d_isLattice_536 (coe v0)))
-- Algebra.Lattice.Bundles.Lattice._.trans
d_trans_552 ::
  T_Lattice_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_552 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe d_isLattice_536 (coe v0)))
-- Algebra.Lattice.Bundles.Lattice._.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_512 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_554 ~v0 ~v1 v2
  = du_'8743''45'absorbs'45''8744'_554 v2
du_'8743''45'absorbs'45''8744'_554 ::
  T_Lattice_512 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_554 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3122
      (coe d_isLattice_536 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∧-assoc
d_'8743''45'assoc_556 ::
  T_Lattice_512 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_556 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
      (coe d_isLattice_536 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∧-comm
d_'8743''45'comm_558 ::
  T_Lattice_512 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_558 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
      (coe d_isLattice_536 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∧-cong
d_'8743''45'cong_560 ::
  T_Lattice_512 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_560 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
      (coe d_isLattice_536 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∧-congʳ
d_'8743''45'cong'691'_562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'691'_562 ~v0 ~v1 v2
  = du_'8743''45'cong'691'_562 v2
du_'8743''45'cong'691'_562 ::
  T_Lattice_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'691'_562 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3128
      (coe d_isLattice_536 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∧-congˡ
d_'8743''45'cong'737'_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'737'_564 ~v0 ~v1 v2
  = du_'8743''45'cong'737'_564 v2
du_'8743''45'cong'737'_564 ::
  T_Lattice_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'737'_564 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
      (coe d_isLattice_536 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_512 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_566 ~v0 ~v1 v2
  = du_'8744''45'absorbs'45''8743'_566 v2
du_'8744''45'absorbs'45''8743'_566 ::
  T_Lattice_512 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_566 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3120
      (coe d_isLattice_536 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∨-assoc
d_'8744''45'assoc_568 ::
  T_Lattice_512 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_568 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
      (coe d_isLattice_536 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∨-comm
d_'8744''45'comm_570 ::
  T_Lattice_512 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_570 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
      (coe d_isLattice_536 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∨-cong
d_'8744''45'cong_572 ::
  T_Lattice_512 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_572 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
      (coe d_isLattice_536 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∨-congʳ
d_'8744''45'cong'691'_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'691'_574 ~v0 ~v1 v2
  = du_'8744''45'cong'691'_574 v2
du_'8744''45'cong'691'_574 ::
  T_Lattice_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'691'_574 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3136
      (coe d_isLattice_536 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∨-congˡ
d_'8744''45'cong'737'_576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'737'_576 ~v0 ~v1 v2
  = du_'8744''45'cong'737'_576 v2
du_'8744''45'cong'737'_576 ::
  T_Lattice_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'737'_576 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3132
      (coe d_isLattice_536 (coe v0))
-- Algebra.Lattice.Bundles.Lattice.rawLattice
d_rawLattice_578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_512 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
d_rawLattice_578 ~v0 ~v1 v2 = du_rawLattice_578 v2
du_rawLattice_578 ::
  T_Lattice_512 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
du_rawLattice_578 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.Raw.C_constructor_42
      (d__'8743'__534 (coe v0)) (d__'8744'__532 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∧-rawMagma
d_'8743''45'rawMagma_582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_512 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'8743''45'rawMagma_582 ~v0 ~v1 v2 = du_'8743''45'rawMagma_582 v2
du_'8743''45'rawMagma_582 ::
  T_Lattice_512 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_'8743''45'rawMagma_582 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
      (coe du_rawLattice_578 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∨-rawMagma
d_'8744''45'rawMagma_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_512 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'8744''45'rawMagma_584 ~v0 ~v1 v2 = du_'8744''45'rawMagma_584 v2
du_'8744''45'rawMagma_584 ::
  T_Lattice_512 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_'8744''45'rawMagma_584 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
      (coe du_rawLattice_578 (coe v0))
-- Algebra.Lattice.Bundles.Lattice.setoid
d_setoid_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_512 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_586 ~v0 ~v1 v2 = du_setoid_586 v2
du_setoid_586 ::
  T_Lattice_512 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_586 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe d_isLattice_536 (coe v0)))
-- Algebra.Lattice.Bundles.Lattice._._≉_
d__'8777'__590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_512 -> AgdaAny -> AgdaAny -> ()
d__'8777'__590 = erased
-- Algebra.Lattice.Bundles.DistributiveLattice
d_DistributiveLattice_598 a0 a1 = ()
data T_DistributiveLattice_598
  = C_constructor_692 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny)
                      MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
-- Algebra.Lattice.Bundles.DistributiveLattice.Carrier
d_Carrier_614 :: T_DistributiveLattice_598 -> ()
d_Carrier_614 = erased
-- Algebra.Lattice.Bundles.DistributiveLattice._≈_
d__'8776'__616 ::
  T_DistributiveLattice_598 -> AgdaAny -> AgdaAny -> ()
d__'8776'__616 = erased
-- Algebra.Lattice.Bundles.DistributiveLattice._∨_
d__'8744'__618 ::
  T_DistributiveLattice_598 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__618 v0
  = case coe v0 of
      C_constructor_692 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.DistributiveLattice._∧_
d__'8743'__620 ::
  T_DistributiveLattice_598 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__620 v0
  = case coe v0 of
      C_constructor_692 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.DistributiveLattice.isDistributiveLattice
d_isDistributiveLattice_622 ::
  T_DistributiveLattice_598 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
d_isDistributiveLattice_622 v0
  = case coe v0 of
      C_constructor_692 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.DistributiveLattice._.absorptive
d_absorptive_626 ::
  T_DistributiveLattice_598 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_626 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3106
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe d_isDistributiveLattice_622 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.isEquivalence
d_isEquivalence_628 ::
  T_DistributiveLattice_598 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_628 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe d_isDistributiveLattice_622 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.isLattice
d_isLattice_630 ::
  T_DistributiveLattice_598 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_isLattice_630 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
      (coe d_isDistributiveLattice_622 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.isPartialEquivalence
d_isPartialEquivalence_632 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_632 ~v0 ~v1 v2
  = du_isPartialEquivalence_632 v2
du_isPartialEquivalence_632 ::
  T_DistributiveLattice_598 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_632 v0
  = let v1 = d_isDistributiveLattice_622 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe v2))))
-- Algebra.Lattice.Bundles.DistributiveLattice._.refl
d_refl_634 :: T_DistributiveLattice_598 -> AgdaAny -> AgdaAny
d_refl_634 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe d_isDistributiveLattice_622 (coe v0))))
-- Algebra.Lattice.Bundles.DistributiveLattice._.reflexive
d_reflexive_636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_636 ~v0 ~v1 v2 = du_reflexive_636 v2
du_reflexive_636 ::
  T_DistributiveLattice_598 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_636 v0
  = let v1 = d_isDistributiveLattice_622 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe
                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                 (coe v2))
              v3))
-- Algebra.Lattice.Bundles.DistributiveLattice._.sym
d_sym_638 ::
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_638 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe d_isDistributiveLattice_622 (coe v0))))
-- Algebra.Lattice.Bundles.DistributiveLattice._.trans
d_trans_640 ::
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_640 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe d_isDistributiveLattice_622 (coe v0))))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_642 ~v0 ~v1 v2
  = du_'8743''45'absorbs'45''8744'_642 v2
du_'8743''45'absorbs'45''8744'_642 ::
  T_DistributiveLattice_598 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_642 v0
  = let v1 = d_isDistributiveLattice_622 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3122
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158 (coe v1)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-assoc
d_'8743''45'assoc_644 ::
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_644 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe d_isDistributiveLattice_622 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-comm
d_'8743''45'comm_646 ::
  T_DistributiveLattice_598 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_646 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe d_isDistributiveLattice_622 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-cong
d_'8743''45'cong_648 ::
  T_DistributiveLattice_598 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_648 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe d_isDistributiveLattice_622 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-congʳ
d_'8743''45'cong'691'_650 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'691'_650 ~v0 ~v1 v2
  = du_'8743''45'cong'691'_650 v2
du_'8743''45'cong'691'_650 ::
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'691'_650 v0
  = let v1 = d_isDistributiveLattice_622 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3128
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158 (coe v1)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-congˡ
d_'8743''45'cong'737'_652 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'737'_652 ~v0 ~v1 v2
  = du_'8743''45'cong'737'_652 v2
du_'8743''45'cong'737'_652 ::
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'737'_652 v0
  = let v1 = d_isDistributiveLattice_622 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158 (coe v1)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-distrib-∨
d_'8743''45'distrib'45''8744'_654 ::
  T_DistributiveLattice_598 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_654 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3162
      (coe d_isDistributiveLattice_622 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-distribʳ-∨
d_'8743''45'distrib'691''45''8744'_656 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'691''45''8744'_656 ~v0 ~v1 v2
  = du_'8743''45'distrib'691''45''8744'_656 v2
du_'8743''45'distrib'691''45''8744'_656 ::
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'691''45''8744'_656 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'691''45''8744'_3210
      (coe d_isDistributiveLattice_622 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_658 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8744'_658 ~v0 ~v1 v2
  = du_'8743''45'distrib'737''45''8744'_658 v2
du_'8743''45'distrib'737''45''8744'_658 ::
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'737''45''8744'_658 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3208
      (coe d_isDistributiveLattice_622 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_660 ~v0 ~v1 v2
  = du_'8744''45'absorbs'45''8743'_660 v2
du_'8744''45'absorbs'45''8743'_660 ::
  T_DistributiveLattice_598 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_660 v0
  = let v1 = d_isDistributiveLattice_622 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3120
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158 (coe v1)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-assoc
d_'8744''45'assoc_662 ::
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_662 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe d_isDistributiveLattice_622 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-comm
d_'8744''45'comm_664 ::
  T_DistributiveLattice_598 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_664 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe d_isDistributiveLattice_622 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-cong
d_'8744''45'cong_666 ::
  T_DistributiveLattice_598 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_666 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe d_isDistributiveLattice_622 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-congʳ
d_'8744''45'cong'691'_668 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'691'_668 ~v0 ~v1 v2
  = du_'8744''45'cong'691'_668 v2
du_'8744''45'cong'691'_668 ::
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'691'_668 v0
  = let v1 = d_isDistributiveLattice_622 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3136
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158 (coe v1)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-congˡ
d_'8744''45'cong'737'_670 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'737'_670 ~v0 ~v1 v2
  = du_'8744''45'cong'737'_670 v2
du_'8744''45'cong'737'_670 ::
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'737'_670 v0
  = let v1 = d_isDistributiveLattice_622 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3132
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158 (coe v1)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-distrib-∧
d_'8744''45'distrib'45''8743'_672 ::
  T_DistributiveLattice_598 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_672 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3160
      (coe d_isDistributiveLattice_622 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_674 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'691''45''8743'_674 ~v0 ~v1 v2
  = du_'8744''45'distrib'691''45''8743'_674 v2
du_'8744''45'distrib'691''45''8743'_674 ::
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'691''45''8743'_674 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3206
      (coe d_isDistributiveLattice_622 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-distribˡ-∧
d_'8744''45'distrib'737''45''8743'_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'737''45''8743'_676 ~v0 ~v1 v2
  = du_'8744''45'distrib'737''45''8743'_676 v2
du_'8744''45'distrib'737''45''8743'_676 ::
  T_DistributiveLattice_598 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'737''45''8743'_676 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'737''45''8743'_3204
      (coe d_isDistributiveLattice_622 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice.lattice
d_lattice_678 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 -> T_Lattice_512
d_lattice_678 ~v0 ~v1 v2 = du_lattice_678 v2
du_lattice_678 :: T_DistributiveLattice_598 -> T_Lattice_512
du_lattice_678 v0
  = coe
      C_constructor_592 (d__'8744'__618 (coe v0))
      (d__'8743'__620 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe d_isDistributiveLattice_622 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._._≉_
d__'8777'__682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 -> AgdaAny -> AgdaAny -> ()
d__'8777'__682 = erased
-- Algebra.Lattice.Bundles.DistributiveLattice._.rawLattice
d_rawLattice_684 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
d_rawLattice_684 ~v0 ~v1 v2 = du_rawLattice_684 v2
du_rawLattice_684 ::
  T_DistributiveLattice_598 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
du_rawLattice_684 v0
  = coe du_rawLattice_578 (coe du_lattice_678 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.setoid
d_setoid_686 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_686 ~v0 ~v1 v2 = du_setoid_686 v2
du_setoid_686 ::
  T_DistributiveLattice_598 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_686 v0 = coe du_setoid_586 (coe du_lattice_678 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-rawMagma
d_'8743''45'rawMagma_688 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'8743''45'rawMagma_688 ~v0 ~v1 v2 = du_'8743''45'rawMagma_688 v2
du_'8743''45'rawMagma_688 ::
  T_DistributiveLattice_598 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_'8743''45'rawMagma_688 v0
  = let v1 = coe du_lattice_678 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe du_rawLattice_578 (coe v1)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-rawMagma
d_'8744''45'rawMagma_690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_598 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'8744''45'rawMagma_690 ~v0 ~v1 v2 = du_'8744''45'rawMagma_690 v2
du_'8744''45'rawMagma_690 ::
  T_DistributiveLattice_598 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_'8744''45'rawMagma_690 v0
  = let v1 = coe du_lattice_678 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe du_rawLattice_578 (coe v1)))
-- Algebra.Lattice.Bundles.BooleanAlgebra
d_BooleanAlgebra_698 a0 a1 = ()
data T_BooleanAlgebra_698
  = C_constructor_822 (AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny) AgdaAny
                      AgdaAny
                      MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224
-- Algebra.Lattice.Bundles.BooleanAlgebra.Carrier
d_Carrier_720 :: T_BooleanAlgebra_698 -> ()
d_Carrier_720 = erased
-- Algebra.Lattice.Bundles.BooleanAlgebra._≈_
d__'8776'__722 :: T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> ()
d__'8776'__722 = erased
-- Algebra.Lattice.Bundles.BooleanAlgebra._∨_
d__'8744'__724 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__724 v0
  = case coe v0 of
      C_constructor_822 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BooleanAlgebra._∧_
d__'8743'__726 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__726 v0
  = case coe v0 of
      C_constructor_822 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BooleanAlgebra.¬_
d_'172'__728 :: T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny
d_'172'__728 v0
  = case coe v0 of
      C_constructor_822 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BooleanAlgebra.⊤
d_'8868'_730 :: T_BooleanAlgebra_698 -> AgdaAny
d_'8868'_730 v0
  = case coe v0 of
      C_constructor_822 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BooleanAlgebra.⊥
d_'8869'_732 :: T_BooleanAlgebra_698 -> AgdaAny
d_'8869'_732 v0
  = case coe v0 of
      C_constructor_822 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BooleanAlgebra.isBooleanAlgebra
d_isBooleanAlgebra_734 ::
  T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3224
d_isBooleanAlgebra_734 v0
  = case coe v0 of
      C_constructor_822 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BooleanAlgebra._.absorptive
d_absorptive_738 ::
  T_BooleanAlgebra_698 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_738 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3106
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
            (coe d_isBooleanAlgebra_734 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.isDistributiveLattice
d_isDistributiveLattice_740 ::
  T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3146
d_isDistributiveLattice_740 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
      (coe d_isBooleanAlgebra_734 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.isEquivalence
d_isEquivalence_742 ::
  T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_742 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
            (coe d_isBooleanAlgebra_734 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.isLattice
d_isLattice_744 ::
  T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_isLattice_744 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
         (coe d_isBooleanAlgebra_734 (coe v0)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.isPartialEquivalence
d_isPartialEquivalence_746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_746 ~v0 ~v1 v2
  = du_isPartialEquivalence_746 v2
du_isPartialEquivalence_746 ::
  T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_746 v0
  = let v1 = d_isBooleanAlgebra_734 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_44
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe v3)))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.refl
d_refl_748 :: T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny
d_refl_748 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe d_isBooleanAlgebra_734 (coe v0)))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.reflexive
d_reflexive_750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_750 ~v0 ~v1 v2 = du_reflexive_750 v2
du_reflexive_750 ::
  T_BooleanAlgebra_698 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_750 v0
  = let v1 = d_isBooleanAlgebra_734 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                    (coe v3))
                 v4)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.sym
d_sym_752 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_752 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe d_isBooleanAlgebra_734 (coe v0)))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.trans
d_trans_754 ::
  T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_754 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
               (coe d_isBooleanAlgebra_734 (coe v0)))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.¬-cong
d_'172''45'cong_756 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'cong_756 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3250
      (coe d_isBooleanAlgebra_734 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_758 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_758 ~v0 ~v1 v2
  = du_'8743''45'absorbs'45''8744'_758 v2
du_'8743''45'absorbs'45''8744'_758 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_758 v0
  = let v1 = d_isBooleanAlgebra_734 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3122
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe v2))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-assoc
d_'8743''45'assoc_760 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_760 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
            (coe d_isBooleanAlgebra_734 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-comm
d_'8743''45'comm_762 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_762 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
            (coe d_isBooleanAlgebra_734 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-complement
d_'8743''45'complement_764 ::
  T_BooleanAlgebra_698 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'complement_764 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'complement_3248
      (coe d_isBooleanAlgebra_734 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-complementʳ
d_'8743''45'complement'691'_766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny
d_'8743''45'complement'691'_766 ~v0 ~v1 v2
  = du_'8743''45'complement'691'_766 v2
du_'8743''45'complement'691'_766 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny
du_'8743''45'complement'691'_766 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3312
      (coe d_isBooleanAlgebra_734 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-complementˡ
d_'8743''45'complement'737'_768 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny
d_'8743''45'complement'737'_768 ~v0 ~v1 v2
  = du_'8743''45'complement'737'_768 v2
du_'8743''45'complement'737'_768 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny
du_'8743''45'complement'737'_768 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'737'_3310
      (coe d_isBooleanAlgebra_734 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-cong
d_'8743''45'cong_770 ::
  T_BooleanAlgebra_698 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_770 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
            (coe d_isBooleanAlgebra_734 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-congʳ
d_'8743''45'cong'691'_772 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'691'_772 ~v0 ~v1 v2
  = du_'8743''45'cong'691'_772 v2
du_'8743''45'cong'691'_772 ::
  T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'691'_772 v0
  = let v1 = d_isBooleanAlgebra_734 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3128
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe v2))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-congˡ
d_'8743''45'cong'737'_774 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'737'_774 ~v0 ~v1 v2
  = du_'8743''45'cong'737'_774 v2
du_'8743''45'cong'737'_774 ::
  T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'737'_774 v0
  = let v1 = d_isBooleanAlgebra_734 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe v2))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-distrib-∨
d_'8743''45'distrib'45''8744'_776 ::
  T_BooleanAlgebra_698 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_776 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3162
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
         (coe d_isBooleanAlgebra_734 (coe v0)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-distribʳ-∨
d_'8743''45'distrib'691''45''8744'_778 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'691''45''8744'_778 ~v0 ~v1 v2
  = du_'8743''45'distrib'691''45''8744'_778 v2
du_'8743''45'distrib'691''45''8744'_778 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'691''45''8744'_778 v0
  = let v1 = d_isBooleanAlgebra_734 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'691''45''8744'_3210
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
            (coe v1)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8744'_780 ~v0 ~v1 v2
  = du_'8743''45'distrib'737''45''8744'_780 v2
du_'8743''45'distrib'737''45''8744'_780 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'737''45''8744'_780 v0
  = let v1 = d_isBooleanAlgebra_734 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3208
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
            (coe v1)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_782 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_782 ~v0 ~v1 v2
  = du_'8744''45'absorbs'45''8743'_782 v2
du_'8744''45'absorbs'45''8743'_782 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_782 v0
  = let v1 = d_isBooleanAlgebra_734 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3120
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe v2))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-assoc
d_'8744''45'assoc_784 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_784 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
            (coe d_isBooleanAlgebra_734 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-comm
d_'8744''45'comm_786 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_786 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
            (coe d_isBooleanAlgebra_734 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-complement
d_'8744''45'complement_788 ::
  T_BooleanAlgebra_698 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'complement_788 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'complement_3246
      (coe d_isBooleanAlgebra_734 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-complementʳ
d_'8744''45'complement'691'_790 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny
d_'8744''45'complement'691'_790 ~v0 ~v1 v2
  = du_'8744''45'complement'691'_790 v2
du_'8744''45'complement'691'_790 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny
du_'8744''45'complement'691'_790 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3308
      (coe d_isBooleanAlgebra_734 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-complementˡ
d_'8744''45'complement'737'_792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny
d_'8744''45'complement'737'_792 ~v0 ~v1 v2
  = du_'8744''45'complement'737'_792 v2
du_'8744''45'complement'737'_792 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny
du_'8744''45'complement'737'_792 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'737'_3306
      (coe d_isBooleanAlgebra_734 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-cong
d_'8744''45'cong_794 ::
  T_BooleanAlgebra_698 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_794 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
            (coe d_isBooleanAlgebra_734 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-congʳ
d_'8744''45'cong'691'_796 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'691'_796 ~v0 ~v1 v2
  = du_'8744''45'cong'691'_796 v2
du_'8744''45'cong'691'_796 ::
  T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'691'_796 v0
  = let v1 = d_isBooleanAlgebra_734 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3136
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe v2))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-congˡ
d_'8744''45'cong'737'_798 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'737'_798 ~v0 ~v1 v2
  = du_'8744''45'cong'737'_798 v2
du_'8744''45'cong'737'_798 ::
  T_BooleanAlgebra_698 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'737'_798 v0
  = let v1 = d_isBooleanAlgebra_734 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3132
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3158
               (coe v2))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-distrib-∧
d_'8744''45'distrib'45''8743'_800 ::
  T_BooleanAlgebra_698 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_800 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3160
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
         (coe d_isBooleanAlgebra_734 (coe v0)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'691''45''8743'_802 ~v0 ~v1 v2
  = du_'8744''45'distrib'691''45''8743'_802 v2
du_'8744''45'distrib'691''45''8743'_802 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'691''45''8743'_802 v0
  = let v1 = d_isBooleanAlgebra_734 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3206
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
            (coe v1)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-distribˡ-∧
d_'8744''45'distrib'737''45''8743'_804 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'737''45''8743'_804 ~v0 ~v1 v2
  = du_'8744''45'distrib'737''45''8743'_804 v2
du_'8744''45'distrib'737''45''8743'_804 ::
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'737''45''8743'_804 v0
  = let v1 = d_isBooleanAlgebra_734 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'737''45''8743'_3204
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
            (coe v1)))
-- Algebra.Lattice.Bundles.BooleanAlgebra.distributiveLattice
d_distributiveLattice_806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 -> T_DistributiveLattice_598
d_distributiveLattice_806 ~v0 ~v1 v2
  = du_distributiveLattice_806 v2
du_distributiveLattice_806 ::
  T_BooleanAlgebra_698 -> T_DistributiveLattice_598
du_distributiveLattice_806 v0
  = coe
      C_constructor_692 (d__'8744'__724 (coe v0))
      (d__'8743'__726 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3244
         (coe d_isBooleanAlgebra_734 (coe v0)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._._≉_
d__'8777'__810 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 -> AgdaAny -> AgdaAny -> ()
d__'8777'__810 = erased
-- Algebra.Lattice.Bundles.BooleanAlgebra._.lattice
d_lattice_812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 -> T_Lattice_512
d_lattice_812 ~v0 ~v1 v2 = du_lattice_812 v2
du_lattice_812 :: T_BooleanAlgebra_698 -> T_Lattice_512
du_lattice_812 v0
  = coe du_lattice_678 (coe du_distributiveLattice_806 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.rawLattice
d_rawLattice_814 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
d_rawLattice_814 ~v0 ~v1 v2 = du_rawLattice_814 v2
du_rawLattice_814 ::
  T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
du_rawLattice_814 v0
  = let v1 = coe du_distributiveLattice_806 (coe v0) in
    coe (coe du_rawLattice_578 (coe du_lattice_678 (coe v1)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.setoid
d_setoid_816 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_816 ~v0 ~v1 v2 = du_setoid_816 v2
du_setoid_816 ::
  T_BooleanAlgebra_698 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_816 v0
  = let v1 = coe du_distributiveLattice_806 (coe v0) in
    coe (coe du_setoid_586 (coe du_lattice_678 (coe v1)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-rawMagma
d_'8743''45'rawMagma_818 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'8743''45'rawMagma_818 ~v0 ~v1 v2 = du_'8743''45'rawMagma_818 v2
du_'8743''45'rawMagma_818 ::
  T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_'8743''45'rawMagma_818 v0
  = let v1 = coe du_distributiveLattice_806 (coe v0) in
    coe
      (let v2 = coe du_lattice_678 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
            (coe du_rawLattice_578 (coe v2))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-rawMagma
d_'8744''45'rawMagma_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'8744''45'rawMagma_820 ~v0 ~v1 v2 = du_'8744''45'rawMagma_820 v2
du_'8744''45'rawMagma_820 ::
  T_BooleanAlgebra_698 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_'8744''45'rawMagma_820 v0
  = let v1 = coe du_distributiveLattice_806 (coe v0) in
    coe
      (let v2 = coe du_lattice_678 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
            (coe du_rawLattice_578 (coe v2))))
