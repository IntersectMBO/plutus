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

module MAlonzo.Code.Algebra.Lattice.Bundles where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Bundles.Raw qualified
import MAlonzo.Code.Algebra.Lattice.Bundles.Raw qualified
import MAlonzo.Code.Algebra.Lattice.Structures qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Lattice.Bundles.Semilattice
d_Semilattice_10 a0 a1 = ()
data T_Semilattice_10
  = C_Semilattice'46'constructor_193 (AgdaAny -> AgdaAny -> AgdaAny)
                                     MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
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
      C_Semilattice'46'constructor_193 v3 v4 -> coe v3
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.Semilattice.isSemilattice
d_isSemilattice_30 ::
  T_Semilattice_10 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_isSemilattice_30 v0
  = case coe v0 of
      C_Semilattice'46'constructor_193 v3 v4 -> coe v4
      _                                      -> MAlonzo.RTE.mazUnreachableError
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
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))
-- Algebra.Lattice.Bundles.Semilattice._.comm
d_comm_36 :: T_Semilattice_10 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_36 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_600
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
         MAlonzo.Code.Algebra.Structures.d_idem_518
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))
-- Algebra.Lattice.Bundles.Semilattice._.isBand
d_isBand_40 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_isBand_40 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isBand_598
      (coe d_isSemilattice_30 (coe v0))
-- Algebra.Lattice.Bundles.Semilattice._.isEquivalence
d_isEquivalence_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_42 ~v0 ~v1 v2 = du_isEquivalence_42 v2
du_isEquivalence_42 ::
  T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_42 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))))
-- Algebra.Lattice.Bundles.Semilattice._.isMagma
d_isMagma_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_44 ~v0 ~v1 v2 = du_isMagma_44 v2
du_isMagma_44 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_44 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))
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
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))))
-- Algebra.Lattice.Bundles.Semilattice._.isSemigroup
d_isSemigroup_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_48 ~v0 ~v1 v2 = du_isSemigroup_48 v2
du_isSemigroup_48 ::
  T_Semilattice_10 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_48 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))
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
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))))
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
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))
                    v5))))
-- Algebra.Lattice.Bundles.Semilattice._.setoid
d_setoid_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_54 ~v0 ~v1 v2 = du_setoid_54 v2
du_setoid_54 ::
  T_Semilattice_10 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_54 v0
  = let v1 = d_isSemilattice_30 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_200
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3)))))
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
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))))
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
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))))
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
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))))
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
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3)))))
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
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3)))))
-- Algebra.Lattice.Bundles.Semilattice.band
d_band_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.T_Band_596
d_band_66 ~v0 ~v1 v2 = du_band_66 v2
du_band_66 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.T_Band_596
du_band_66 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Band'46'constructor_10881
      (d__'8729'__28 (coe v0))
      (MAlonzo.Code.Algebra.Structures.d_isBand_598
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
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_isBand_72 ~v0 ~v1 v2 = du_isBand_72 v2
du_isBand_72 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_isBand_72 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isBand_598
      (coe d_isSemilattice_30 (coe v0))
-- Algebra.Lattice.Bundles.Semilattice._.isMagma
d_isMagma_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_74 ~v0 ~v1 v2 = du_isMagma_74 v2
du_isMagma_74 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_74 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
         (coe
            MAlonzo.Code.Algebra.Structures.d_isBand_598
            (coe d_isSemilattice_30 (coe v0))))
-- Algebra.Lattice.Bundles.Semilattice._.isSemigroup
d_isSemigroup_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_76 ~v0 ~v1 v2 = du_isSemigroup_76 v2
du_isSemigroup_76 ::
  T_Semilattice_10 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_76 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
      (coe
         MAlonzo.Code.Algebra.Structures.d_isBand_598
         (coe d_isSemilattice_30 (coe v0)))
-- Algebra.Lattice.Bundles.Semilattice._.magma
d_magma_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_magma_78 ~v0 ~v1 v2 = du_magma_78 v2
du_magma_78 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.T_Magma_68
du_magma_78 v0
  = let v1 = coe du_band_66 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_magma_584
         (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_648 (coe v1)))
-- Algebra.Lattice.Bundles.Semilattice._.rawMagma
d_rawMagma_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_rawMagma_80 ~v0 ~v1 v2 = du_rawMagma_80 v2
du_rawMagma_80 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_rawMagma_80 v0
  = let v1 = coe du_band_66 (coe v0) in
    coe
      (let v2
             = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_648 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_rawMagma_112
            (coe MAlonzo.Code.Algebra.Bundles.du_magma_584 (coe v2))))
-- Algebra.Lattice.Bundles.Semilattice._.semigroup
d_semigroup_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_semigroup_82 ~v0 ~v1 v2 = du_semigroup_82 v2
du_semigroup_82 ::
  T_Semilattice_10 -> MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_semigroup_82 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.du_semigroup_648
      (coe du_band_66 (coe v0))
-- Algebra.Lattice.Bundles.MeetSemilattice
d_MeetSemilattice_88 a0 a1 = ()
data T_MeetSemilattice_88
  = C_MeetSemilattice'46'constructor_1393 (AgdaAny ->
                                           AgdaAny -> AgdaAny)
                                          MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
-- Algebra.Lattice.Bundles.MeetSemilattice.Carrier
d_Carrier_102 :: T_MeetSemilattice_88 -> ()
d_Carrier_102 = erased
-- Algebra.Lattice.Bundles.MeetSemilattice._≈_
d__'8776'__104 :: T_MeetSemilattice_88 -> AgdaAny -> AgdaAny -> ()
d__'8776'__104 = erased
-- Algebra.Lattice.Bundles.MeetSemilattice._∧_
d__'8743'__106 ::
  T_MeetSemilattice_88 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__106 v0
  = case coe v0 of
      C_MeetSemilattice'46'constructor_1393 v3 v4 -> coe v3
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.MeetSemilattice.isMeetSemilattice
d_isMeetSemilattice_108 ::
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_isMeetSemilattice_108 v0
  = case coe v0 of
      C_MeetSemilattice'46'constructor_1393 v3 v4 -> coe v4
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.MeetSemilattice._.assoc
d_assoc_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_112 ~v0 ~v1 v2 = du_assoc_112 v2
du_assoc_112 ::
  T_MeetSemilattice_88 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_112 v0
  = let v1 = d_isMeetSemilattice_108 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.comm
d_comm_114 :: T_MeetSemilattice_88 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_114 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_600
      (coe d_isMeetSemilattice_108 (coe v0))
-- Algebra.Lattice.Bundles.MeetSemilattice._.idem
d_idem_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 -> AgdaAny -> AgdaAny
d_idem_116 ~v0 ~v1 v2 = du_idem_116 v2
du_idem_116 :: T_MeetSemilattice_88 -> AgdaAny -> AgdaAny
du_idem_116 v0
  = let v1 = d_isMeetSemilattice_108 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_idem_518
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))
-- Algebra.Lattice.Bundles.MeetSemilattice._.isBand
d_isBand_118 ::
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_isBand_118 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isBand_598
      (coe d_isMeetSemilattice_108 (coe v0))
-- Algebra.Lattice.Bundles.MeetSemilattice._.isEquivalence
d_isEquivalence_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_120 ~v0 ~v1 v2 = du_isEquivalence_120 v2
du_isEquivalence_120 ::
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_120 v0
  = let v1 = d_isMeetSemilattice_108 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.isMagma
d_isMagma_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_122 ~v0 ~v1 v2 = du_isMagma_122 v2
du_isMagma_122 ::
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_122 v0
  = let v1 = d_isMeetSemilattice_108 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.isPartialEquivalence
d_isPartialEquivalence_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_124 ~v0 ~v1 v2
  = du_isPartialEquivalence_124 v2
du_isPartialEquivalence_124 ::
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_124 v0
  = let v1 = d_isMeetSemilattice_108 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.isSemigroup
d_isSemigroup_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_126 ~v0 ~v1 v2 = du_isSemigroup_126 v2
du_isSemigroup_126 ::
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_126 v0
  = let v1 = d_isMeetSemilattice_108 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))
-- Algebra.Lattice.Bundles.MeetSemilattice._.refl
d_refl_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 -> AgdaAny -> AgdaAny
d_refl_128 ~v0 ~v1 v2 = du_refl_128 v2
du_refl_128 :: T_MeetSemilattice_88 -> AgdaAny -> AgdaAny
du_refl_128 v0
  = let v1 = d_isMeetSemilattice_108 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.reflexive
d_reflexive_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_130 ~v0 ~v1 v2 = du_reflexive_130 v2
du_reflexive_130 ::
  T_MeetSemilattice_88 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_130 v0
  = let v1 = d_isMeetSemilattice_108 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))
                    v5))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.setoid
d_setoid_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_132 ~v0 ~v1 v2 = du_setoid_132 v2
du_setoid_132 ::
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_132 v0
  = let v1 = d_isMeetSemilattice_108 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_200
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3)))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.sym
d_sym_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_134 ~v0 ~v1 v2 = du_sym_134 v2
du_sym_134 ::
  T_MeetSemilattice_88 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_134 v0
  = let v1 = d_isMeetSemilattice_108 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.trans
d_trans_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_136 ~v0 ~v1 v2 = du_trans_136 v2
du_trans_136 ::
  T_MeetSemilattice_88 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_136 v0
  = let v1 = d_isMeetSemilattice_108 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.∙-cong
d_'8729''45'cong_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_138 ~v0 ~v1 v2 = du_'8729''45'cong_138 v2
du_'8729''45'cong_138 ::
  T_MeetSemilattice_88 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_138 v0
  = let v1 = d_isMeetSemilattice_108 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.∙-congʳ
d_'8729''45'cong'691'_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_140 ~v0 ~v1 v2
  = du_'8729''45'cong'691'_140 v2
du_'8729''45'cong'691'_140 ::
  T_MeetSemilattice_88 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_140 v0
  = let v1 = d_isMeetSemilattice_108 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3)))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.∙-congˡ
d_'8729''45'cong'737'_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_142 ~v0 ~v1 v2
  = du_'8729''45'cong'737'_142 v2
du_'8729''45'cong'737'_142 ::
  T_MeetSemilattice_88 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_142 v0
  = let v1 = d_isMeetSemilattice_108 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3)))))
-- Algebra.Lattice.Bundles.MeetSemilattice.semilattice
d_semilattice_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 -> T_Semilattice_10
d_semilattice_144 ~v0 ~v1 v2 = du_semilattice_144 v2
du_semilattice_144 :: T_MeetSemilattice_88 -> T_Semilattice_10
du_semilattice_144 v0
  = coe
      C_Semilattice'46'constructor_193 (d__'8743'__106 (coe v0))
      (d_isMeetSemilattice_108 (coe v0))
-- Algebra.Lattice.Bundles.MeetSemilattice._.band
d_band_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 -> MAlonzo.Code.Algebra.Bundles.T_Band_596
d_band_148 ~v0 ~v1 v2 = du_band_148 v2
du_band_148 ::
  T_MeetSemilattice_88 -> MAlonzo.Code.Algebra.Bundles.T_Band_596
du_band_148 v0 = coe du_band_66 (coe du_semilattice_144 (coe v0))
-- Algebra.Lattice.Bundles.MeetSemilattice._.magma
d_magma_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 -> MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_magma_150 ~v0 ~v1 v2 = du_magma_150 v2
du_magma_150 ::
  T_MeetSemilattice_88 -> MAlonzo.Code.Algebra.Bundles.T_Magma_68
du_magma_150 v0
  = let v1 = coe du_semilattice_144 (coe v0) in
    coe
      (let v2 = coe du_band_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_magma_584
            (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_648 (coe v2))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.rawMagma
d_rawMagma_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_rawMagma_152 ~v0 ~v1 v2 = du_rawMagma_152 v2
du_rawMagma_152 ::
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_rawMagma_152 v0
  = let v1 = coe du_semilattice_144 (coe v0) in
    coe
      (let v2 = coe du_band_66 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_648 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_rawMagma_112
               (coe MAlonzo.Code.Algebra.Bundles.du_magma_584 (coe v3)))))
-- Algebra.Lattice.Bundles.MeetSemilattice._.semigroup
d_semigroup_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_semigroup_154 ~v0 ~v1 v2 = du_semigroup_154 v2
du_semigroup_154 ::
  T_MeetSemilattice_88 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_semigroup_154 v0
  = let v1 = coe du_semilattice_144 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_semigroup_648
         (coe du_band_66 (coe v1)))
-- Algebra.Lattice.Bundles.JoinSemilattice
d_JoinSemilattice_160 a0 a1 = ()
data T_JoinSemilattice_160
  = C_JoinSemilattice'46'constructor_2531 (AgdaAny ->
                                           AgdaAny -> AgdaAny)
                                          MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
-- Algebra.Lattice.Bundles.JoinSemilattice.Carrier
d_Carrier_174 :: T_JoinSemilattice_160 -> ()
d_Carrier_174 = erased
-- Algebra.Lattice.Bundles.JoinSemilattice._≈_
d__'8776'__176 :: T_JoinSemilattice_160 -> AgdaAny -> AgdaAny -> ()
d__'8776'__176 = erased
-- Algebra.Lattice.Bundles.JoinSemilattice._∨_
d__'8744'__178 ::
  T_JoinSemilattice_160 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__178 v0
  = case coe v0 of
      C_JoinSemilattice'46'constructor_2531 v3 v4 -> coe v3
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.JoinSemilattice.isJoinSemilattice
d_isJoinSemilattice_180 ::
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_isJoinSemilattice_180 v0
  = case coe v0 of
      C_JoinSemilattice'46'constructor_2531 v3 v4 -> coe v4
      _                                           -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.JoinSemilattice._.assoc
d_assoc_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_184 ~v0 ~v1 v2 = du_assoc_184 v2
du_assoc_184 ::
  T_JoinSemilattice_160 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_184 v0
  = let v1 = d_isJoinSemilattice_180 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.comm
d_comm_186 ::
  T_JoinSemilattice_160 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_186 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_600
      (coe d_isJoinSemilattice_180 (coe v0))
-- Algebra.Lattice.Bundles.JoinSemilattice._.idem
d_idem_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 -> AgdaAny -> AgdaAny
d_idem_188 ~v0 ~v1 v2 = du_idem_188 v2
du_idem_188 :: T_JoinSemilattice_160 -> AgdaAny -> AgdaAny
du_idem_188 v0
  = let v1 = d_isJoinSemilattice_180 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_idem_518
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))
-- Algebra.Lattice.Bundles.JoinSemilattice._.isBand
d_isBand_190 ::
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_isBand_190 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isBand_598
      (coe d_isJoinSemilattice_180 (coe v0))
-- Algebra.Lattice.Bundles.JoinSemilattice._.isEquivalence
d_isEquivalence_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_192 ~v0 ~v1 v2 = du_isEquivalence_192 v2
du_isEquivalence_192 ::
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_192 v0
  = let v1 = d_isJoinSemilattice_180 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.isMagma
d_isMagma_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_194 ~v0 ~v1 v2 = du_isMagma_194 v2
du_isMagma_194 ::
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_194 v0
  = let v1 = d_isJoinSemilattice_180 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.isPartialEquivalence
d_isPartialEquivalence_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_196 ~v0 ~v1 v2
  = du_isPartialEquivalence_196 v2
du_isPartialEquivalence_196 ::
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_196 v0
  = let v1 = d_isJoinSemilattice_180 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.isSemigroup
d_isSemigroup_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_198 ~v0 ~v1 v2 = du_isSemigroup_198 v2
du_isSemigroup_198 ::
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_198 v0
  = let v1 = d_isJoinSemilattice_180 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
         (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))
-- Algebra.Lattice.Bundles.JoinSemilattice._.refl
d_refl_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 -> AgdaAny -> AgdaAny
d_refl_200 ~v0 ~v1 v2 = du_refl_200 v2
du_refl_200 :: T_JoinSemilattice_160 -> AgdaAny -> AgdaAny
du_refl_200 v0
  = let v1 = d_isJoinSemilattice_180 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.reflexive
d_reflexive_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_202 ~v0 ~v1 v2 = du_reflexive_202 v2
du_reflexive_202 ::
  T_JoinSemilattice_160 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_202 v0
  = let v1 = d_isJoinSemilattice_180 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (let v4 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3) in
             coe
               (\ v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                    (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v4))
                    v5))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.setoid
d_setoid_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_204 ~v0 ~v1 v2 = du_setoid_204 v2
du_setoid_204 ::
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_204 v0
  = let v1 = d_isJoinSemilattice_180 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_setoid_200
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3)))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.sym
d_sym_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_206 ~v0 ~v1 v2 = du_sym_206 v2
du_sym_206 ::
  T_JoinSemilattice_160 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_206 v0
  = let v1 = d_isJoinSemilattice_180 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.trans
d_trans_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_208 ~v0 ~v1 v2 = du_trans_208 v2
du_trans_208 ::
  T_JoinSemilattice_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_208 v0
  = let v1 = d_isJoinSemilattice_180 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1))))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.∙-cong
d_'8729''45'cong_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_210 ~v0 ~v1 v2 = du_'8729''45'cong_210 v2
du_'8729''45'cong_210 ::
  T_JoinSemilattice_160 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_210 v0
  = let v1 = d_isJoinSemilattice_180 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1)))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.∙-congʳ
d_'8729''45'cong'691'_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_212 ~v0 ~v1 v2
  = du_'8729''45'cong'691'_212 v2
du_'8729''45'cong'691'_212 ::
  T_JoinSemilattice_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_212 v0
  = let v1 = d_isJoinSemilattice_180 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3)))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.∙-congˡ
d_'8729''45'cong'737'_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_214 ~v0 ~v1 v2
  = du_'8729''45'cong'737'_214 v2
du_'8729''45'cong'737'_214 ::
  T_JoinSemilattice_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_214 v0
  = let v1 = d_isJoinSemilattice_180 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
               (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v3)))))
-- Algebra.Lattice.Bundles.JoinSemilattice.semilattice
d_semilattice_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 -> T_Semilattice_10
d_semilattice_216 ~v0 ~v1 v2 = du_semilattice_216 v2
du_semilattice_216 :: T_JoinSemilattice_160 -> T_Semilattice_10
du_semilattice_216 v0
  = coe
      C_Semilattice'46'constructor_193 (d__'8744'__178 (coe v0))
      (d_isJoinSemilattice_180 (coe v0))
-- Algebra.Lattice.Bundles.JoinSemilattice._.band
d_band_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 -> MAlonzo.Code.Algebra.Bundles.T_Band_596
d_band_220 ~v0 ~v1 v2 = du_band_220 v2
du_band_220 ::
  T_JoinSemilattice_160 -> MAlonzo.Code.Algebra.Bundles.T_Band_596
du_band_220 v0 = coe du_band_66 (coe du_semilattice_216 (coe v0))
-- Algebra.Lattice.Bundles.JoinSemilattice._.magma
d_magma_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 -> MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_magma_222 ~v0 ~v1 v2 = du_magma_222 v2
du_magma_222 ::
  T_JoinSemilattice_160 -> MAlonzo.Code.Algebra.Bundles.T_Magma_68
du_magma_222 v0
  = let v1 = coe du_semilattice_216 (coe v0) in
    coe
      (let v2 = coe du_band_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_magma_584
            (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_648 (coe v2))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.rawMagma
d_rawMagma_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_rawMagma_224 ~v0 ~v1 v2 = du_rawMagma_224 v2
du_rawMagma_224 ::
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_rawMagma_224 v0
  = let v1 = coe du_semilattice_216 (coe v0) in
    coe
      (let v2 = coe du_band_66 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_648 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_rawMagma_112
               (coe MAlonzo.Code.Algebra.Bundles.du_magma_584 (coe v3)))))
-- Algebra.Lattice.Bundles.JoinSemilattice._.semigroup
d_semigroup_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_semigroup_226 ~v0 ~v1 v2 = du_semigroup_226 v2
du_semigroup_226 ::
  T_JoinSemilattice_160 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_semigroup_226 v0
  = let v1 = coe du_semilattice_216 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_semigroup_648
         (coe du_band_66 (coe v1)))
-- Algebra.Lattice.Bundles.BoundedSemilattice
d_BoundedSemilattice_232 a0 a1 = ()
data T_BoundedSemilattice_232
  = C_BoundedSemilattice'46'constructor_3703 (AgdaAny ->
                                              AgdaAny -> AgdaAny)
                                             AgdaAny
                                             MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852
-- Algebra.Lattice.Bundles.BoundedSemilattice.Carrier
d_Carrier_248 :: T_BoundedSemilattice_232 -> ()
d_Carrier_248 = erased
-- Algebra.Lattice.Bundles.BoundedSemilattice._≈_
d__'8776'__250 ::
  T_BoundedSemilattice_232 -> AgdaAny -> AgdaAny -> ()
d__'8776'__250 = erased
-- Algebra.Lattice.Bundles.BoundedSemilattice._∙_
d__'8729'__252 ::
  T_BoundedSemilattice_232 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8729'__252 v0
  = case coe v0 of
      C_BoundedSemilattice'46'constructor_3703 v3 v4 v5 -> coe v3
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedSemilattice.ε
d_ε_254 :: T_BoundedSemilattice_232 -> AgdaAny
d_ε_254 v0
  = case coe v0 of
      C_BoundedSemilattice'46'constructor_3703 v3 v4 v5 -> coe v4
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedSemilattice.isBoundedSemilattice
d_isBoundedSemilattice_256 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852
d_isBoundedSemilattice_256 v0
  = case coe v0 of
      C_BoundedSemilattice'46'constructor_3703 v3 v4 v5 -> coe v5
      _                                                 -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedSemilattice._.assoc
d_assoc_260 ::
  T_BoundedSemilattice_232 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_260 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_482
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
               (coe d_isBoundedSemilattice_256 (coe v0)))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.comm
d_comm_262 ::
  T_BoundedSemilattice_232 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_262 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_comm_748
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
         (coe d_isBoundedSemilattice_256 (coe v0)))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.idem
d_idem_264 :: T_BoundedSemilattice_232 -> AgdaAny -> AgdaAny
d_idem_264 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_idem_864
      (coe d_isBoundedSemilattice_256 (coe v0))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.identity
d_identity_266 ::
  T_BoundedSemilattice_232 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_266 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
            (coe d_isBoundedSemilattice_256 (coe v0))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.identityʳ
d_identity'691'_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 -> AgdaAny -> AgdaAny
d_identity'691'_268 ~v0 ~v1 v2 = du_identity'691'_268 v2
du_identity'691'_268 ::
  T_BoundedSemilattice_232 -> AgdaAny -> AgdaAny
du_identity'691'_268 v0
  = let v1 = d_isBoundedSemilattice_256 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'691'_728
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.identityˡ
d_identity'737'_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 -> AgdaAny -> AgdaAny
d_identity'737'_270 ~v0 ~v1 v2 = du_identity'737'_270 v2
du_identity'737'_270 ::
  T_BoundedSemilattice_232 -> AgdaAny -> AgdaAny
du_identity'737'_270 v0
  = let v1 = d_isBoundedSemilattice_256 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'737'_726
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isBand
d_isBand_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_isBand_272 ~v0 ~v1 v2 = du_isBand_272 v2
du_isBand_272 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_isBand_272 v0
  = let v1 = d_isBoundedSemilattice_256 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isBand_846
         (coe
            MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_910
            (coe v1)))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isCommutativeMagma
d_isCommutativeMagma_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_212
d_isCommutativeMagma_274 ~v0 ~v1 v2 = du_isCommutativeMagma_274 v2
du_isCommutativeMagma_274 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_212
du_isCommutativeMagma_274 v0
  = let v1 = d_isBoundedSemilattice_256 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_586
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_786
               (coe v2))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isCommutativeMonoid
d_isCommutativeMonoid_276 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_736
d_isCommutativeMonoid_276 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
      (coe d_isBoundedSemilattice_256 (coe v0))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isCommutativeSemigroup
d_isCommutativeSemigroup_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
d_isCommutativeSemigroup_278 ~v0 ~v1 v2
  = du_isCommutativeSemigroup_278 v2
du_isCommutativeSemigroup_278 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_548
du_isCommutativeSemigroup_278 v0
  = let v1 = d_isBoundedSemilattice_256 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_786
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
            (coe v1)))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isEquivalence
d_isEquivalence_280 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_280 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                  (coe d_isBoundedSemilattice_256 (coe v0))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isIdempotentMonoid
d_isIdempotentMonoid_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796
d_isIdempotentMonoid_282 ~v0 ~v1 v2 = du_isIdempotentMonoid_282 v2
du_isIdempotentMonoid_282 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentMonoid_796
du_isIdempotentMonoid_282 v0
  = let v1 = d_isBoundedSemilattice_256 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isIdempotentMonoid_910 (coe v1))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isMagma
d_isMagma_284 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_284 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMagma_480
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_746
            (coe
               MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
               (coe d_isBoundedSemilattice_256 (coe v0)))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isMonoid
d_isMonoid_286 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_isMonoid_286 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isMonoid_746
      (coe
         MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
         (coe d_isBoundedSemilattice_256 (coe v0)))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isPartialEquivalence
d_isPartialEquivalence_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_288 ~v0 ~v1 v2
  = du_isPartialEquivalence_288 v2
du_isPartialEquivalence_288 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_288 v0
  = let v1 = d_isBoundedSemilattice_256 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5)))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isSemigroup
d_isSemigroup_290 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_290 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
            (coe d_isBoundedSemilattice_256 (coe v0))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isCommutativeBand
d_isCommutativeBand_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_isCommutativeBand_292 ~v0 ~v1 v2 = du_isCommutativeBand_292 v2
du_isCommutativeBand_292 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
du_isCommutativeBand_292 v0
  = let v1 = d_isBoundedSemilattice_256 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916 (coe v1))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.isUnitalMagma
d_isUnitalMagma_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642
d_isUnitalMagma_294 ~v0 ~v1 v2 = du_isUnitalMagma_294 v2
du_isUnitalMagma_294 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_642
du_isUnitalMagma_294 v0
  = let v1 = d_isBoundedSemilattice_256 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_730
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.refl
d_refl_296 :: T_BoundedSemilattice_232 -> AgdaAny -> AgdaAny
d_refl_296 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_746
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                     (coe d_isBoundedSemilattice_256 (coe v0)))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.reflexive
d_reflexive_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_298 ~v0 ~v1 v2 = du_reflexive_298 v2
du_reflexive_298 ::
  T_BoundedSemilattice_232 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_298 v0
  = let v1 = d_isBoundedSemilattice_256 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                       (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))
                       v6)))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.setoid
d_setoid_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_300 ~v0 ~v1 v2 = du_setoid_300 v2
du_setoid_300 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_300 v0
  = let v1 = d_isBoundedSemilattice_256 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.sym
d_sym_302 ::
  T_BoundedSemilattice_232 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_302 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_746
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                     (coe d_isBoundedSemilattice_256 (coe v0)))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.trans
d_trans_304 ::
  T_BoundedSemilattice_232 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_304 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_746
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                     (coe d_isBoundedSemilattice_256 (coe v0)))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.∙-cong
d_'8729''45'cong_306 ::
  T_BoundedSemilattice_232 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_306 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_746
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                  (coe d_isBoundedSemilattice_256 (coe v0))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.∙-congʳ
d_'8729''45'cong'691'_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_308 ~v0 ~v1 v2
  = du_'8729''45'cong'691'_308 v2
du_'8729''45'cong'691'_308 ::
  T_BoundedSemilattice_232 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_308 v0
  = let v1 = d_isBoundedSemilattice_256 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.∙-congˡ
d_'8729''45'cong'737'_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_310 ~v0 ~v1 v2
  = du_'8729''45'cong'737'_310 v2
du_'8729''45'cong'737'_310 ::
  T_BoundedSemilattice_232 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_310 v0
  = let v1 = d_isBoundedSemilattice_256 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedSemilattice.semilattice
d_semilattice_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 -> T_Semilattice_10
d_semilattice_312 ~v0 ~v1 v2 = du_semilattice_312 v2
du_semilattice_312 :: T_BoundedSemilattice_232 -> T_Semilattice_10
du_semilattice_312 v0
  = coe
      C_Semilattice'46'constructor_193 (d__'8729'__252 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
         (coe d_isBoundedSemilattice_256 (coe v0)))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.band
d_band_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 -> MAlonzo.Code.Algebra.Bundles.T_Band_596
d_band_316 ~v0 ~v1 v2 = du_band_316 v2
du_band_316 ::
  T_BoundedSemilattice_232 -> MAlonzo.Code.Algebra.Bundles.T_Band_596
du_band_316 v0 = coe du_band_66 (coe du_semilattice_312 (coe v0))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.magma
d_magma_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 -> MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_magma_318 ~v0 ~v1 v2 = du_magma_318 v2
du_magma_318 ::
  T_BoundedSemilattice_232 -> MAlonzo.Code.Algebra.Bundles.T_Magma_68
du_magma_318 v0
  = let v1 = coe du_semilattice_312 (coe v0) in
    coe
      (let v2 = coe du_band_66 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_magma_584
            (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_648 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.rawMagma
d_rawMagma_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_rawMagma_320 ~v0 ~v1 v2 = du_rawMagma_320 v2
du_rawMagma_320 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_rawMagma_320 v0
  = let v1 = coe du_semilattice_312 (coe v0) in
    coe
      (let v2 = coe du_band_66 (coe v1) in
       coe
         (let v3
                = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_648 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_rawMagma_112
               (coe MAlonzo.Code.Algebra.Bundles.du_magma_584 (coe v3)))))
-- Algebra.Lattice.Bundles.BoundedSemilattice._.semigroup
d_semigroup_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_semigroup_322 ~v0 ~v1 v2 = du_semigroup_322 v2
du_semigroup_322 ::
  T_BoundedSemilattice_232 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_semigroup_322 v0
  = let v1 = coe du_semilattice_312 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Bundles.du_semigroup_648
         (coe du_band_66 (coe v1)))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice
d_BoundedMeetSemilattice_328 a0 a1 = ()
data T_BoundedMeetSemilattice_328
  = C_BoundedMeetSemilattice'46'constructor_5171 (AgdaAny ->
                                                  AgdaAny -> AgdaAny)
                                                 AgdaAny
                                                 MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice.Carrier
d_Carrier_344 :: T_BoundedMeetSemilattice_328 -> ()
d_Carrier_344 = erased
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._≈_
d__'8776'__346 ::
  T_BoundedMeetSemilattice_328 -> AgdaAny -> AgdaAny -> ()
d__'8776'__346 = erased
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._∧_
d__'8743'__348 ::
  T_BoundedMeetSemilattice_328 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__348 v0
  = case coe v0 of
      C_BoundedMeetSemilattice'46'constructor_5171 v3 v4 v5 -> coe v3
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice.⊤
d_'8868'_350 :: T_BoundedMeetSemilattice_328 -> AgdaAny
d_'8868'_350 v0
  = case coe v0 of
      C_BoundedMeetSemilattice'46'constructor_5171 v3 v4 v5 -> coe v4
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice.isBoundedMeetSemilattice
d_isBoundedMeetSemilattice_352 ::
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852
d_isBoundedMeetSemilattice_352 v0
  = case coe v0 of
      C_BoundedMeetSemilattice'46'constructor_5171 v3 v4 v5 -> coe v5
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.assoc
d_assoc_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_356 ~v0 ~v1 v2 = du_assoc_356 v2
du_assoc_356 ::
  T_BoundedMeetSemilattice_328 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_356 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2)))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.comm
d_comm_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_358 ~v0 ~v1 v2 = du_comm_358 v2
du_comm_358 ::
  T_BoundedMeetSemilattice_328 -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_358 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_comm_600
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916 (coe v1)))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.idem
d_idem_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 -> AgdaAny -> AgdaAny
d_idem_360 ~v0 ~v1 v2 = du_idem_360 v2
du_idem_360 :: T_BoundedMeetSemilattice_328 -> AgdaAny -> AgdaAny
du_idem_360 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_idem_518
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.identity
d_identity_362 ::
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_362 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
            (coe d_isBoundedMeetSemilattice_352 (coe v0))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.identityʳ
d_identity'691'_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 -> AgdaAny -> AgdaAny
d_identity'691'_364 ~v0 ~v1 v2 = du_identity'691'_364 v2
du_identity'691'_364 ::
  T_BoundedMeetSemilattice_328 -> AgdaAny -> AgdaAny
du_identity'691'_364 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'691'_728
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.identityˡ
d_identity'737'_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 -> AgdaAny -> AgdaAny
d_identity'737'_366 ~v0 ~v1 v2 = du_identity'737'_366 v2
du_identity'737'_366 ::
  T_BoundedMeetSemilattice_328 -> AgdaAny -> AgdaAny
du_identity'737'_366 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'737'_726
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.isBand
d_isBand_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_isBand_368 ~v0 ~v1 v2 = du_isBand_368 v2
du_isBand_368 ::
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_isBand_368 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isBand_598
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916 (coe v1)))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.isEquivalence
d_isEquivalence_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_370 ~v0 ~v1 v2 = du_isEquivalence_370 v2
du_isEquivalence_370 ::
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_370 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.isMagma
d_isMagma_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_372 ~v0 ~v1 v2 = du_isMagma_372 v2
du_isMagma_372 ::
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_372 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2)))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.isCommutativeBand
d_isCommutativeBand_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_isCommutativeBand_374 ~v0 ~v1 v2 = du_isCommutativeBand_374 v2
du_isCommutativeBand_374 ::
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
du_isCommutativeBand_374 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916 (coe v1))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.isPartialEquivalence
d_isPartialEquivalence_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_376 ~v0 ~v1 v2
  = du_isPartialEquivalence_376 v2
du_isPartialEquivalence_376 ::
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_376 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5)))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.isSemigroup
d_isSemigroup_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_378 ~v0 ~v1 v2 = du_isSemigroup_378 v2
du_isSemigroup_378 ::
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_378 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.refl
d_refl_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 -> AgdaAny -> AgdaAny
d_refl_380 ~v0 ~v1 v2 = du_refl_380 v2
du_refl_380 :: T_BoundedMeetSemilattice_328 -> AgdaAny -> AgdaAny
du_refl_380 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_480
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                     (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2)))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.reflexive
d_reflexive_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_382 ~v0 ~v1 v2 = du_reflexive_382 v2
du_reflexive_382 ::
  T_BoundedMeetSemilattice_328 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_382 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                       (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))
                       v6)))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.setoid
d_setoid_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_384 ~v0 ~v1 v2 = du_setoid_384 v2
du_setoid_384 ::
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_384 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.sym
d_sym_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_386 ~v0 ~v1 v2 = du_sym_386 v2
du_sym_386 ::
  T_BoundedMeetSemilattice_328 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_386 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_480
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                     (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2)))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.trans
d_trans_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_388 ~v0 ~v1 v2 = du_trans_388 v2
du_trans_388 ::
  T_BoundedMeetSemilattice_328 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_388 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_480
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                     (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2)))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.∙-cong
d_'8729''45'cong_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_390 ~v0 ~v1 v2 = du_'8729''45'cong_390 v2
du_'8729''45'cong_390 ::
  T_BoundedMeetSemilattice_328 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_390 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.∙-congʳ
d_'8729''45'cong'691'_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_392 ~v0 ~v1 v2
  = du_'8729''45'cong'691'_392 v2
du_'8729''45'cong'691'_392 ::
  T_BoundedMeetSemilattice_328 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_392 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.∙-congˡ
d_'8729''45'cong'737'_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_394 ~v0 ~v1 v2
  = du_'8729''45'cong'737'_394 v2
du_'8729''45'cong'737'_394 ::
  T_BoundedMeetSemilattice_328 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_394 v0
  = let v1 = d_isBoundedMeetSemilattice_352 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice.boundedSemilattice
d_boundedSemilattice_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 -> T_BoundedSemilattice_232
d_boundedSemilattice_396 ~v0 ~v1 v2 = du_boundedSemilattice_396 v2
du_boundedSemilattice_396 ::
  T_BoundedMeetSemilattice_328 -> T_BoundedSemilattice_232
du_boundedSemilattice_396 v0
  = coe
      C_BoundedSemilattice'46'constructor_3703 (d__'8743'__348 (coe v0))
      (d_'8868'_350 (coe v0)) (d_isBoundedMeetSemilattice_352 (coe v0))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.band
d_band_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_596
d_band_400 ~v0 ~v1 v2 = du_band_400 v2
du_band_400 ::
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_596
du_band_400 v0
  = let v1 = coe du_boundedSemilattice_396 (coe v0) in
    coe (coe du_band_66 (coe du_semilattice_312 (coe v1)))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.magma
d_magma_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_magma_402 ~v0 ~v1 v2 = du_magma_402 v2
du_magma_402 ::
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
du_magma_402 v0
  = let v1 = coe du_boundedSemilattice_396 (coe v0) in
    coe
      (let v2 = coe du_semilattice_312 (coe v1) in
       coe
         (let v3 = coe du_band_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_magma_584
               (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_648 (coe v3)))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.rawMagma
d_rawMagma_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_rawMagma_404 ~v0 ~v1 v2 = du_rawMagma_404 v2
du_rawMagma_404 ::
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_rawMagma_404 v0
  = let v1 = coe du_boundedSemilattice_396 (coe v0) in
    coe
      (let v2 = coe du_semilattice_312 (coe v1) in
       coe
         (let v3 = coe du_band_66 (coe v2) in
          coe
            (let v4
                   = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_648 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_rawMagma_112
                  (coe MAlonzo.Code.Algebra.Bundles.du_magma_584 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.semigroup
d_semigroup_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_semigroup_406 ~v0 ~v1 v2 = du_semigroup_406 v2
du_semigroup_406 ::
  T_BoundedMeetSemilattice_328 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_semigroup_406 v0
  = let v1 = coe du_boundedSemilattice_396 (coe v0) in
    coe
      (let v2 = coe du_semilattice_312 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_semigroup_648
            (coe du_band_66 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedMeetSemilattice._.semilattice
d_semilattice_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedMeetSemilattice_328 -> T_Semilattice_10
d_semilattice_408 ~v0 ~v1 v2 = du_semilattice_408 v2
du_semilattice_408 ::
  T_BoundedMeetSemilattice_328 -> T_Semilattice_10
du_semilattice_408 v0
  = coe du_semilattice_312 (coe du_boundedSemilattice_396 (coe v0))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice
d_BoundedJoinSemilattice_414 a0 a1 = ()
data T_BoundedJoinSemilattice_414
  = C_BoundedJoinSemilattice'46'constructor_6531 (AgdaAny ->
                                                  AgdaAny -> AgdaAny)
                                                 AgdaAny
                                                 MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice.Carrier
d_Carrier_430 :: T_BoundedJoinSemilattice_414 -> ()
d_Carrier_430 = erased
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._≈_
d__'8776'__432 ::
  T_BoundedJoinSemilattice_414 -> AgdaAny -> AgdaAny -> ()
d__'8776'__432 = erased
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._∨_
d__'8744'__434 ::
  T_BoundedJoinSemilattice_414 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__434 v0
  = case coe v0 of
      C_BoundedJoinSemilattice'46'constructor_6531 v3 v4 v5 -> coe v3
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice.⊥
d_'8869'_436 :: T_BoundedJoinSemilattice_414 -> AgdaAny
d_'8869'_436 v0
  = case coe v0 of
      C_BoundedJoinSemilattice'46'constructor_6531 v3 v4 v5 -> coe v4
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice.isBoundedJoinSemilattice
d_isBoundedJoinSemilattice_438 ::
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Structures.T_IsIdempotentCommutativeMonoid_852
d_isBoundedJoinSemilattice_438 v0
  = case coe v0 of
      C_BoundedJoinSemilattice'46'constructor_6531 v3 v4 v5 -> coe v5
      _                                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.assoc
d_assoc_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_442 ~v0 ~v1 v2 = du_assoc_442 v2
du_assoc_442 ::
  T_BoundedJoinSemilattice_414 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_442 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_482
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2)))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.comm
d_comm_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_444 ~v0 ~v1 v2 = du_comm_444 v2
du_comm_444 ::
  T_BoundedJoinSemilattice_414 -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_444 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_comm_600
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916 (coe v1)))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.idem
d_idem_446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 -> AgdaAny -> AgdaAny
d_idem_446 ~v0 ~v1 v2 = du_idem_446 v2
du_idem_446 :: T_BoundedJoinSemilattice_414 -> AgdaAny -> AgdaAny
du_idem_446 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_idem_518
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.identity
d_identity_448 ::
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_448 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_identity_698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_746
         (coe
            MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
            (coe d_isBoundedJoinSemilattice_438 (coe v0))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.identityʳ
d_identity'691'_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 -> AgdaAny -> AgdaAny
d_identity'691'_450 ~v0 ~v1 v2 = du_identity'691'_450 v2
du_identity'691'_450 ::
  T_BoundedJoinSemilattice_414 -> AgdaAny -> AgdaAny
du_identity'691'_450 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'691'_728
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.identityˡ
d_identity'737'_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 -> AgdaAny -> AgdaAny
d_identity'737'_452 ~v0 ~v1 v2 = du_identity'737'_452 v2
du_identity'737'_452 ::
  T_BoundedJoinSemilattice_414 -> AgdaAny -> AgdaAny
du_identity'737'_452 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Structures.d_isCommutativeMonoid_862
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'737'_726
            (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_746 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.isBand
d_isBand_454 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_isBand_454 ~v0 ~v1 v2 = du_isBand_454 v2
du_isBand_454 ::
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_isBand_454 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isBand_598
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916 (coe v1)))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.isEquivalence
d_isEquivalence_456 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_456 ~v0 ~v1 v2 = du_isEquivalence_456 v2
du_isEquivalence_456 ::
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_456 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.isCommutativeBand
d_isCommutativeBand_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_isCommutativeBand_458 ~v0 ~v1 v2 = du_isCommutativeBand_458 v2
du_isCommutativeBand_458 ::
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
du_isCommutativeBand_458 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916 (coe v1))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.isMagma
d_isMagma_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_460 ~v0 ~v1 v2 = du_isMagma_460 v2
du_isMagma_460 ::
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_460 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
               (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2)))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.isPartialEquivalence
d_isPartialEquivalence_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_462 ~v0 ~v1 v2
  = du_isPartialEquivalence_462 v2
du_isPartialEquivalence_462 ::
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_462 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5)))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.isSemigroup
d_isSemigroup_464 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_464 ~v0 ~v1 v2 = du_isSemigroup_464 v2
du_isSemigroup_464 ::
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_isSemigroup_464 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
            (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.refl
d_refl_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 -> AgdaAny -> AgdaAny
d_refl_466 ~v0 ~v1 v2 = du_refl_466 v2
du_refl_466 :: T_BoundedJoinSemilattice_414 -> AgdaAny -> AgdaAny
du_refl_466 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_480
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                     (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2)))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.reflexive
d_reflexive_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_468 ~v0 ~v1 v2 = du_reflexive_468 v2
du_reflexive_468 ::
  T_BoundedJoinSemilattice_414 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_468 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v3) in
             coe
               (let v5 = MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4) in
                coe
                  (\ v6 v7 v8 ->
                     coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                       (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v5))
                       v6)))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.setoid
d_setoid_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_470 ~v0 ~v1 v2 = du_setoid_470 v2
du_setoid_470 ::
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_470 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.sym
d_sym_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_472 ~v0 ~v1 v2 = du_sym_472 v2
du_sym_472 ::
  T_BoundedJoinSemilattice_414 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_472 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_480
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                     (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2)))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.trans
d_trans_474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_474 ~v0 ~v1 v2 = du_trans_474 v2
du_trans_474 ::
  T_BoundedJoinSemilattice_414 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_474 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_480
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                     (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2)))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.∙-cong
d_'8729''45'cong_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_476 ~v0 ~v1 v2 = du_'8729''45'cong_476 v2
du_'8729''45'cong_476 ::
  T_BoundedJoinSemilattice_414 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_476 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_516
                  (coe MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.∙-congʳ
d_'8729''45'cong'691'_478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_478 ~v0 ~v1 v2
  = du_'8729''45'cong'691'_478 v2
du_'8729''45'cong'691'_478 ::
  T_BoundedJoinSemilattice_414 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_478 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.∙-congˡ
d_'8729''45'cong'737'_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_480 ~v0 ~v1 v2
  = du_'8729''45'cong'737'_480 v2
du_'8729''45'cong'737'_480 ::
  T_BoundedJoinSemilattice_414 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_480 v0
  = let v1 = d_isBoundedJoinSemilattice_438 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeBand_916
                 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isBand_598 (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice.boundedSemilattice
d_boundedSemilattice_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 -> T_BoundedSemilattice_232
d_boundedSemilattice_482 ~v0 ~v1 v2 = du_boundedSemilattice_482 v2
du_boundedSemilattice_482 ::
  T_BoundedJoinSemilattice_414 -> T_BoundedSemilattice_232
du_boundedSemilattice_482 v0
  = coe
      C_BoundedSemilattice'46'constructor_3703 (d__'8744'__434 (coe v0))
      (d_'8869'_436 (coe v0)) (d_isBoundedJoinSemilattice_438 (coe v0))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.band
d_band_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_596
d_band_486 ~v0 ~v1 v2 = du_band_486 v2
du_band_486 ::
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_596
du_band_486 v0
  = let v1 = coe du_boundedSemilattice_482 (coe v0) in
    coe (coe du_band_66 (coe du_semilattice_312 (coe v1)))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.magma
d_magma_488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
d_magma_488 ~v0 ~v1 v2 = du_magma_488 v2
du_magma_488 ::
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_68
du_magma_488 v0
  = let v1 = coe du_boundedSemilattice_482 (coe v0) in
    coe
      (let v2 = coe du_semilattice_312 (coe v1) in
       coe
         (let v3 = coe du_band_66 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Bundles.du_magma_584
               (coe MAlonzo.Code.Algebra.Bundles.du_semigroup_648 (coe v3)))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.rawMagma
d_rawMagma_490 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_rawMagma_490 ~v0 ~v1 v2 = du_rawMagma_490 v2
du_rawMagma_490 ::
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_rawMagma_490 v0
  = let v1 = coe du_boundedSemilattice_482 (coe v0) in
    coe
      (let v2 = coe du_semilattice_312 (coe v1) in
       coe
         (let v3 = coe du_band_66 (coe v2) in
          coe
            (let v4
                   = coe MAlonzo.Code.Algebra.Bundles.du_semigroup_648 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Bundles.du_rawMagma_112
                  (coe MAlonzo.Code.Algebra.Bundles.du_magma_584 (coe v4))))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.semigroup
d_semigroup_492 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_semigroup_492 ~v0 ~v1 v2 = du_semigroup_492 v2
du_semigroup_492 ::
  T_BoundedJoinSemilattice_414 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_semigroup_492 v0
  = let v1 = coe du_boundedSemilattice_482 (coe v0) in
    coe
      (let v2 = coe du_semilattice_312 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Bundles.du_semigroup_648
            (coe du_band_66 (coe v2))))
-- Algebra.Lattice.Bundles.BoundedJoinSemilattice._.semilattice
d_semilattice_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BoundedJoinSemilattice_414 -> T_Semilattice_10
d_semilattice_494 ~v0 ~v1 v2 = du_semilattice_494 v2
du_semilattice_494 ::
  T_BoundedJoinSemilattice_414 -> T_Semilattice_10
du_semilattice_494 v0
  = coe du_semilattice_312 (coe du_boundedSemilattice_482 (coe v0))
-- Algebra.Lattice.Bundles.Lattice
d_Lattice_500 a0 a1 = ()
data T_Lattice_500
  = C_Lattice'46'constructor_7925 (AgdaAny -> AgdaAny -> AgdaAny)
                                  (AgdaAny -> AgdaAny -> AgdaAny)
                                  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
-- Algebra.Lattice.Bundles.Lattice.Carrier
d_Carrier_516 :: T_Lattice_500 -> ()
d_Carrier_516 = erased
-- Algebra.Lattice.Bundles.Lattice._≈_
d__'8776'__518 :: T_Lattice_500 -> AgdaAny -> AgdaAny -> ()
d__'8776'__518 = erased
-- Algebra.Lattice.Bundles.Lattice._∨_
d__'8744'__520 :: T_Lattice_500 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__520 v0
  = case coe v0 of
      C_Lattice'46'constructor_7925 v3 v4 v5 -> coe v3
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.Lattice._∧_
d__'8743'__522 :: T_Lattice_500 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__522 v0
  = case coe v0 of
      C_Lattice'46'constructor_7925 v3 v4 v5 -> coe v4
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.Lattice.isLattice
d_isLattice_524 ::
  T_Lattice_500 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
d_isLattice_524 v0
  = case coe v0 of
      C_Lattice'46'constructor_7925 v3 v4 v5 -> coe v5
      _                                      -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.Lattice._.absorptive
d_absorptive_528 ::
  T_Lattice_500 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_528 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_2998
      (coe d_isLattice_524 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.isEquivalence
d_isEquivalence_530 ::
  T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_530 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
      (coe d_isLattice_524 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.isPartialEquivalence
d_isPartialEquivalence_532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_532 ~v0 ~v1 v2
  = du_isPartialEquivalence_532 v2
du_isPartialEquivalence_532 ::
  T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_532 v0
  = let v1 = d_isLattice_524 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
            (coe v1)))
-- Algebra.Lattice.Bundles.Lattice._.refl
d_refl_534 :: T_Lattice_500 -> AgdaAny -> AgdaAny
d_refl_534 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe d_isLattice_524 (coe v0)))
-- Algebra.Lattice.Bundles.Lattice._.reflexive
d_reflexive_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_500 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_536 ~v0 ~v1 v2 = du_reflexive_536 v2
du_reflexive_536 ::
  T_Lattice_500 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_536 v0
  = let v1 = d_isLattice_524 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe
              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
              (coe v1))
           v2)
-- Algebra.Lattice.Bundles.Lattice._.sym
d_sym_538 ::
  T_Lattice_500 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_538 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe d_isLattice_524 (coe v0)))
-- Algebra.Lattice.Bundles.Lattice._.trans
d_trans_540 ::
  T_Lattice_500 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_540 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe d_isLattice_524 (coe v0)))
-- Algebra.Lattice.Bundles.Lattice._.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_500 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_542 ~v0 ~v1 v2
  = du_'8743''45'absorbs'45''8744'_542 v2
du_'8743''45'absorbs'45''8744'_542 ::
  T_Lattice_500 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_542 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3014
      (coe d_isLattice_524 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∧-assoc
d_'8743''45'assoc_544 ::
  T_Lattice_500 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_544 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
      (coe d_isLattice_524 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∧-comm
d_'8743''45'comm_546 ::
  T_Lattice_500 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_546 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
      (coe d_isLattice_524 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∧-cong
d_'8743''45'cong_548 ::
  T_Lattice_500 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_548 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
      (coe d_isLattice_524 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∧-congʳ
d_'8743''45'cong'691'_550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_500 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'691'_550 ~v0 ~v1 v2
  = du_'8743''45'cong'691'_550 v2
du_'8743''45'cong'691'_550 ::
  T_Lattice_500 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'691'_550 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3020
      (coe d_isLattice_524 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∧-congˡ
d_'8743''45'cong'737'_552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_500 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'737'_552 ~v0 ~v1 v2
  = du_'8743''45'cong'737'_552 v2
du_'8743''45'cong'737'_552 ::
  T_Lattice_500 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'737'_552 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
      (coe d_isLattice_524 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_500 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_554 ~v0 ~v1 v2
  = du_'8744''45'absorbs'45''8743'_554 v2
du_'8744''45'absorbs'45''8743'_554 ::
  T_Lattice_500 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_554 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3012
      (coe d_isLattice_524 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∨-assoc
d_'8744''45'assoc_556 ::
  T_Lattice_500 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_556 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_2988
      (coe d_isLattice_524 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∨-comm
d_'8744''45'comm_558 ::
  T_Lattice_500 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_558 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
      (coe d_isLattice_524 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∨-cong
d_'8744''45'cong_560 ::
  T_Lattice_500 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_560 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
      (coe d_isLattice_524 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∨-congʳ
d_'8744''45'cong'691'_562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_500 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'691'_562 ~v0 ~v1 v2
  = du_'8744''45'cong'691'_562 v2
du_'8744''45'cong'691'_562 ::
  T_Lattice_500 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'691'_562 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3028
      (coe d_isLattice_524 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∨-congˡ
d_'8744''45'cong'737'_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_500 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'737'_564 ~v0 ~v1 v2
  = du_'8744''45'cong'737'_564 v2
du_'8744''45'cong'737'_564 ::
  T_Lattice_500 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'737'_564 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3024
      (coe d_isLattice_524 (coe v0))
-- Algebra.Lattice.Bundles.Lattice.rawLattice
d_rawLattice_566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_500 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
d_rawLattice_566 ~v0 ~v1 v2 = du_rawLattice_566 v2
du_rawLattice_566 ::
  T_Lattice_500 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
du_rawLattice_566 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.Raw.C_RawLattice'46'constructor_121
      (d__'8743'__522 (coe v0)) (d__'8744'__520 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∧-rawMagma
d_'8743''45'rawMagma_570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_500 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'8743''45'rawMagma_570 ~v0 ~v1 v2 = du_'8743''45'rawMagma_570 v2
du_'8743''45'rawMagma_570 ::
  T_Lattice_500 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_'8743''45'rawMagma_570 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
      (coe du_rawLattice_566 (coe v0))
-- Algebra.Lattice.Bundles.Lattice._.∨-rawMagma
d_'8744''45'rawMagma_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_500 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'8744''45'rawMagma_572 ~v0 ~v1 v2 = du_'8744''45'rawMagma_572 v2
du_'8744''45'rawMagma_572 ::
  T_Lattice_500 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_'8744''45'rawMagma_572 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
      (coe du_rawLattice_566 (coe v0))
-- Algebra.Lattice.Bundles.Lattice.setoid
d_setoid_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_500 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_574 ~v0 ~v1 v2 = du_setoid_574 v2
du_setoid_574 ::
  T_Lattice_500 -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_574 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_733
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe d_isLattice_524 (coe v0)))
-- Algebra.Lattice.Bundles.Lattice._._≉_
d__'8777'__578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_Lattice_500 -> AgdaAny -> AgdaAny -> ()
d__'8777'__578 = erased
-- Algebra.Lattice.Bundles.DistributiveLattice
d_DistributiveLattice_584 a0 a1 = ()
data T_DistributiveLattice_584
  = C_DistributiveLattice'46'constructor_9515 (AgdaAny ->
                                               AgdaAny -> AgdaAny)
                                              (AgdaAny -> AgdaAny -> AgdaAny)
                                              MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036
-- Algebra.Lattice.Bundles.DistributiveLattice.Carrier
d_Carrier_600 :: T_DistributiveLattice_584 -> ()
d_Carrier_600 = erased
-- Algebra.Lattice.Bundles.DistributiveLattice._≈_
d__'8776'__602 ::
  T_DistributiveLattice_584 -> AgdaAny -> AgdaAny -> ()
d__'8776'__602 = erased
-- Algebra.Lattice.Bundles.DistributiveLattice._∨_
d__'8744'__604 ::
  T_DistributiveLattice_584 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__604 v0
  = case coe v0 of
      C_DistributiveLattice'46'constructor_9515 v3 v4 v5 -> coe v3
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.DistributiveLattice._∧_
d__'8743'__606 ::
  T_DistributiveLattice_584 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__606 v0
  = case coe v0 of
      C_DistributiveLattice'46'constructor_9515 v3 v4 v5 -> coe v4
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.DistributiveLattice.isDistributiveLattice
d_isDistributiveLattice_608 ::
  T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036
d_isDistributiveLattice_608 v0
  = case coe v0 of
      C_DistributiveLattice'46'constructor_9515 v3 v4 v5 -> coe v5
      _                                                  -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.DistributiveLattice._.absorptive
d_absorptive_612 ::
  T_DistributiveLattice_584 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_612 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_2998
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe d_isDistributiveLattice_608 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.isEquivalence
d_isEquivalence_614 ::
  T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_614 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe d_isDistributiveLattice_608 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.isLattice
d_isLattice_616 ::
  T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
d_isLattice_616 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
      (coe d_isDistributiveLattice_608 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.isPartialEquivalence
d_isPartialEquivalence_618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_618 ~v0 ~v1 v2
  = du_isPartialEquivalence_618 v2
du_isPartialEquivalence_618 ::
  T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_618 v0
  = let v1 = d_isDistributiveLattice_608 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
               (coe v2))))
-- Algebra.Lattice.Bundles.DistributiveLattice._.refl
d_refl_620 :: T_DistributiveLattice_584 -> AgdaAny -> AgdaAny
d_refl_620 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe d_isDistributiveLattice_608 (coe v0))))
-- Algebra.Lattice.Bundles.DistributiveLattice._.reflexive
d_reflexive_622 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_622 ~v0 ~v1 v2 = du_reflexive_622 v2
du_reflexive_622 ::
  T_DistributiveLattice_584 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_622 v0
  = let v1 = d_isDistributiveLattice_608 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                 (coe v1) in
       coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
              (coe
                 MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                 (coe v2))
              v3))
-- Algebra.Lattice.Bundles.DistributiveLattice._.sym
d_sym_624 ::
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_624 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe d_isDistributiveLattice_608 (coe v0))))
-- Algebra.Lattice.Bundles.DistributiveLattice._.trans
d_trans_626 ::
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_626 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe d_isDistributiveLattice_608 (coe v0))))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_628 ~v0 ~v1 v2
  = du_'8743''45'absorbs'45''8744'_628 v2
du_'8743''45'absorbs'45''8744'_628 ::
  T_DistributiveLattice_584 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_628 v0
  = let v1 = d_isDistributiveLattice_608 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3014
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v1)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-assoc
d_'8743''45'assoc_630 ::
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_630 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe d_isDistributiveLattice_608 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-comm
d_'8743''45'comm_632 ::
  T_DistributiveLattice_584 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_632 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe d_isDistributiveLattice_608 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-cong
d_'8743''45'cong_634 ::
  T_DistributiveLattice_584 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_634 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe d_isDistributiveLattice_608 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-congʳ
d_'8743''45'cong'691'_636 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'691'_636 ~v0 ~v1 v2
  = du_'8743''45'cong'691'_636 v2
du_'8743''45'cong'691'_636 ::
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'691'_636 v0
  = let v1 = d_isDistributiveLattice_608 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3020
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v1)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-congˡ
d_'8743''45'cong'737'_638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'737'_638 ~v0 ~v1 v2
  = du_'8743''45'cong'737'_638 v2
du_'8743''45'cong'737'_638 ::
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'737'_638 v0
  = let v1 = d_isDistributiveLattice_608 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v1)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-distrib-∨
d_'8743''45'distrib'45''8744'_640 ::
  T_DistributiveLattice_584 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_640 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3052
      (coe d_isDistributiveLattice_608 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-distribʳ-∨
d_'8743''45'distrib'691''45''8744'_642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'691''45''8744'_642 ~v0 ~v1 v2
  = du_'8743''45'distrib'691''45''8744'_642 v2
du_'8743''45'distrib'691''45''8744'_642 ::
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'691''45''8744'_642 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'691''45''8744'_3100
      (coe d_isDistributiveLattice_608 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_644 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8744'_644 ~v0 ~v1 v2
  = du_'8743''45'distrib'737''45''8744'_644 v2
du_'8743''45'distrib'737''45''8744'_644 ::
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'737''45''8744'_644 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3098
      (coe d_isDistributiveLattice_608 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_646 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_646 ~v0 ~v1 v2
  = du_'8744''45'absorbs'45''8743'_646 v2
du_'8744''45'absorbs'45''8743'_646 ::
  T_DistributiveLattice_584 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_646 v0
  = let v1 = d_isDistributiveLattice_608 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3012
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v1)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-assoc
d_'8744''45'assoc_648 ::
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_648 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_2988
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe d_isDistributiveLattice_608 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-comm
d_'8744''45'comm_650 ::
  T_DistributiveLattice_584 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_650 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe d_isDistributiveLattice_608 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-cong
d_'8744''45'cong_652 ::
  T_DistributiveLattice_584 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_652 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe d_isDistributiveLattice_608 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-congʳ
d_'8744''45'cong'691'_654 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'691'_654 ~v0 ~v1 v2
  = du_'8744''45'cong'691'_654 v2
du_'8744''45'cong'691'_654 ::
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'691'_654 v0
  = let v1 = d_isDistributiveLattice_608 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3028
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v1)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-congˡ
d_'8744''45'cong'737'_656 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'737'_656 ~v0 ~v1 v2
  = du_'8744''45'cong'737'_656 v2
du_'8744''45'cong'737'_656 ::
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'737'_656 v0
  = let v1 = d_isDistributiveLattice_608 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3024
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048 (coe v1)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-distrib-∧
d_'8744''45'distrib'45''8743'_658 ::
  T_DistributiveLattice_584 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_658 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3050
      (coe d_isDistributiveLattice_608 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_660 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'691''45''8743'_660 ~v0 ~v1 v2
  = du_'8744''45'distrib'691''45''8743'_660 v2
du_'8744''45'distrib'691''45''8743'_660 ::
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'691''45''8743'_660 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3096
      (coe d_isDistributiveLattice_608 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-distribˡ-∧
d_'8744''45'distrib'737''45''8743'_662 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'737''45''8743'_662 ~v0 ~v1 v2
  = du_'8744''45'distrib'737''45''8743'_662 v2
du_'8744''45'distrib'737''45''8743'_662 ::
  T_DistributiveLattice_584 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'737''45''8743'_662 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'737''45''8743'_3094
      (coe d_isDistributiveLattice_608 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice.lattice
d_lattice_664 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 -> T_Lattice_500
d_lattice_664 ~v0 ~v1 v2 = du_lattice_664 v2
du_lattice_664 :: T_DistributiveLattice_584 -> T_Lattice_500
du_lattice_664 v0
  = coe
      C_Lattice'46'constructor_7925 (d__'8744'__604 (coe v0))
      (d__'8743'__606 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe d_isDistributiveLattice_608 (coe v0)))
-- Algebra.Lattice.Bundles.DistributiveLattice._._≉_
d__'8777'__668 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 -> AgdaAny -> AgdaAny -> ()
d__'8777'__668 = erased
-- Algebra.Lattice.Bundles.DistributiveLattice._.rawLattice
d_rawLattice_670 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
d_rawLattice_670 ~v0 ~v1 v2 = du_rawLattice_670 v2
du_rawLattice_670 ::
  T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
du_rawLattice_670 v0
  = coe du_rawLattice_566 (coe du_lattice_664 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.setoid
d_setoid_672 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_672 ~v0 ~v1 v2 = du_setoid_672 v2
du_setoid_672 ::
  T_DistributiveLattice_584 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_672 v0 = coe du_setoid_574 (coe du_lattice_664 (coe v0))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∧-rawMagma
d_'8743''45'rawMagma_674 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'8743''45'rawMagma_674 ~v0 ~v1 v2 = du_'8743''45'rawMagma_674 v2
du_'8743''45'rawMagma_674 ::
  T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_'8743''45'rawMagma_674 v0
  = let v1 = coe du_lattice_664 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
         (coe du_rawLattice_566 (coe v1)))
-- Algebra.Lattice.Bundles.DistributiveLattice._.∨-rawMagma
d_'8744''45'rawMagma_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'8744''45'rawMagma_676 ~v0 ~v1 v2 = du_'8744''45'rawMagma_676 v2
du_'8744''45'rawMagma_676 ::
  T_DistributiveLattice_584 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_'8744''45'rawMagma_676 v0
  = let v1 = coe du_lattice_664 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
         (coe du_rawLattice_566 (coe v1)))
-- Algebra.Lattice.Bundles.BooleanAlgebra
d_BooleanAlgebra_682 a0 a1 = ()
data T_BooleanAlgebra_682
  = C_BooleanAlgebra'46'constructor_11509 (AgdaAny ->
                                           AgdaAny -> AgdaAny)
                                          (AgdaAny -> AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                          AgdaAny AgdaAny
                                          MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112
-- Algebra.Lattice.Bundles.BooleanAlgebra.Carrier
d_Carrier_704 :: T_BooleanAlgebra_682 -> ()
d_Carrier_704 = erased
-- Algebra.Lattice.Bundles.BooleanAlgebra._≈_
d__'8776'__706 :: T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> ()
d__'8776'__706 = erased
-- Algebra.Lattice.Bundles.BooleanAlgebra._∨_
d__'8744'__708 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__708 v0
  = case coe v0 of
      C_BooleanAlgebra'46'constructor_11509 v3 v4 v5 v6 v7 v8 -> coe v3
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BooleanAlgebra._∧_
d__'8743'__710 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__710 v0
  = case coe v0 of
      C_BooleanAlgebra'46'constructor_11509 v3 v4 v5 v6 v7 v8 -> coe v4
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BooleanAlgebra.¬_
d_'172'__712 :: T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny
d_'172'__712 v0
  = case coe v0 of
      C_BooleanAlgebra'46'constructor_11509 v3 v4 v5 v6 v7 v8 -> coe v5
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BooleanAlgebra.⊤
d_'8868'_714 :: T_BooleanAlgebra_682 -> AgdaAny
d_'8868'_714 v0
  = case coe v0 of
      C_BooleanAlgebra'46'constructor_11509 v3 v4 v5 v6 v7 v8 -> coe v6
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BooleanAlgebra.⊥
d_'8869'_716 :: T_BooleanAlgebra_682 -> AgdaAny
d_'8869'_716 v0
  = case coe v0 of
      C_BooleanAlgebra'46'constructor_11509 v3 v4 v5 v6 v7 v8 -> coe v7
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BooleanAlgebra.isBooleanAlgebra
d_isBooleanAlgebra_718 ::
  T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3112
d_isBooleanAlgebra_718 v0
  = case coe v0 of
      C_BooleanAlgebra'46'constructor_11509 v3 v4 v5 v6 v7 v8 -> coe v8
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.BooleanAlgebra._.absorptive
d_absorptive_722 ::
  T_BooleanAlgebra_682 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_722 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_2998
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
            (coe d_isBooleanAlgebra_718 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.isDistributiveLattice
d_isDistributiveLattice_724 ::
  T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3036
d_isDistributiveLattice_724 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
      (coe d_isBooleanAlgebra_718 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.isEquivalence
d_isEquivalence_726 ::
  T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_726 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
            (coe d_isBooleanAlgebra_718 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.isLattice
d_isLattice_728 ::
  T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
d_isLattice_728 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
         (coe d_isBooleanAlgebra_718 (coe v0)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.isPartialEquivalence
d_isPartialEquivalence_730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_730 ~v0 ~v1 v2
  = du_isPartialEquivalence_730 v2
du_isPartialEquivalence_730 ::
  T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_730 v0
  = let v1 = d_isBooleanAlgebra_718 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                  (coe v3)))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.refl
d_refl_732 :: T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny
d_refl_732 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe d_isBooleanAlgebra_718 (coe v0)))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.reflexive
d_reflexive_734 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_734 ~v0 ~v1 v2 = du_reflexive_734 v2
du_reflexive_734 ::
  T_BooleanAlgebra_682 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_734 v0
  = let v1 = d_isBooleanAlgebra_718 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                    (coe v3))
                 v4)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.sym
d_sym_736 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_736 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe d_isBooleanAlgebra_718 (coe v0)))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.trans
d_trans_738 ::
  T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_738 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
               (coe d_isBooleanAlgebra_718 (coe v0)))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.¬-cong
d_'172''45'cong_740 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'cong_740 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3138
      (coe d_isBooleanAlgebra_718 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_742 ~v0 ~v1 v2
  = du_'8743''45'absorbs'45''8744'_742 v2
du_'8743''45'absorbs'45''8744'_742 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_742 v0
  = let v1 = d_isBooleanAlgebra_718 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3014
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe v2))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-assoc
d_'8743''45'assoc_744 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_744 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
            (coe d_isBooleanAlgebra_718 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-comm
d_'8743''45'comm_746 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_746 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
            (coe d_isBooleanAlgebra_718 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-complement
d_'8743''45'complement_748 ::
  T_BooleanAlgebra_682 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'complement_748 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'complement_3136
      (coe d_isBooleanAlgebra_718 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-complementʳ
d_'8743''45'complement'691'_750 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny
d_'8743''45'complement'691'_750 ~v0 ~v1 v2
  = du_'8743''45'complement'691'_750 v2
du_'8743''45'complement'691'_750 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny
du_'8743''45'complement'691'_750 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3200
      (coe d_isBooleanAlgebra_718 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-complementˡ
d_'8743''45'complement'737'_752 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny
d_'8743''45'complement'737'_752 ~v0 ~v1 v2
  = du_'8743''45'complement'737'_752 v2
du_'8743''45'complement'737'_752 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny
du_'8743''45'complement'737'_752 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'737'_3198
      (coe d_isBooleanAlgebra_718 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-cong
d_'8743''45'cong_754 ::
  T_BooleanAlgebra_682 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_754 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
            (coe d_isBooleanAlgebra_718 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-congʳ
d_'8743''45'cong'691'_756 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'691'_756 ~v0 ~v1 v2
  = du_'8743''45'cong'691'_756 v2
du_'8743''45'cong'691'_756 ::
  T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'691'_756 v0
  = let v1 = d_isBooleanAlgebra_718 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3020
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe v2))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-congˡ
d_'8743''45'cong'737'_758 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'737'_758 ~v0 ~v1 v2
  = du_'8743''45'cong'737'_758 v2
du_'8743''45'cong'737'_758 ::
  T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'737'_758 v0
  = let v1 = d_isBooleanAlgebra_718 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe v2))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-distrib-∨
d_'8743''45'distrib'45''8744'_760 ::
  T_BooleanAlgebra_682 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_760 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3052
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
         (coe d_isBooleanAlgebra_718 (coe v0)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-distribʳ-∨
d_'8743''45'distrib'691''45''8744'_762 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'691''45''8744'_762 ~v0 ~v1 v2
  = du_'8743''45'distrib'691''45''8744'_762 v2
du_'8743''45'distrib'691''45''8744'_762 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'691''45''8744'_762 v0
  = let v1 = d_isBooleanAlgebra_718 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'691''45''8744'_3100
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
            (coe v1)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8744'_764 ~v0 ~v1 v2
  = du_'8743''45'distrib'737''45''8744'_764 v2
du_'8743''45'distrib'737''45''8744'_764 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'737''45''8744'_764 v0
  = let v1 = d_isBooleanAlgebra_718 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3098
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
            (coe v1)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_766 ~v0 ~v1 v2
  = du_'8744''45'absorbs'45''8743'_766 v2
du_'8744''45'absorbs'45''8743'_766 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_766 v0
  = let v1 = d_isBooleanAlgebra_718 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3012
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe v2))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-assoc
d_'8744''45'assoc_768 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_768 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_2988
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
            (coe d_isBooleanAlgebra_718 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-comm
d_'8744''45'comm_770 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_770 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
            (coe d_isBooleanAlgebra_718 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-complement
d_'8744''45'complement_772 ::
  T_BooleanAlgebra_682 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'complement_772 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'complement_3134
      (coe d_isBooleanAlgebra_718 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-complementʳ
d_'8744''45'complement'691'_774 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny
d_'8744''45'complement'691'_774 ~v0 ~v1 v2
  = du_'8744''45'complement'691'_774 v2
du_'8744''45'complement'691'_774 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny
du_'8744''45'complement'691'_774 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3196
      (coe d_isBooleanAlgebra_718 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-complementˡ
d_'8744''45'complement'737'_776 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny
d_'8744''45'complement'737'_776 ~v0 ~v1 v2
  = du_'8744''45'complement'737'_776 v2
du_'8744''45'complement'737'_776 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny
du_'8744''45'complement'737'_776 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'737'_3194
      (coe d_isBooleanAlgebra_718 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-cong
d_'8744''45'cong_778 ::
  T_BooleanAlgebra_682 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_778 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
            (coe d_isBooleanAlgebra_718 (coe v0))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-congʳ
d_'8744''45'cong'691'_780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'691'_780 ~v0 ~v1 v2
  = du_'8744''45'cong'691'_780 v2
du_'8744''45'cong'691'_780 ::
  T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'691'_780 v0
  = let v1 = d_isBooleanAlgebra_718 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3028
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe v2))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-congˡ
d_'8744''45'cong'737'_782 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'737'_782 ~v0 ~v1 v2
  = du_'8744''45'cong'737'_782 v2
du_'8744''45'cong'737'_782 ::
  T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'737'_782 v0
  = let v1 = d_isBooleanAlgebra_718 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3024
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3048
               (coe v2))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-distrib-∧
d_'8744''45'distrib'45''8743'_784 ::
  T_BooleanAlgebra_682 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_784 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3050
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
         (coe d_isBooleanAlgebra_718 (coe v0)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'691''45''8743'_786 ~v0 ~v1 v2
  = du_'8744''45'distrib'691''45''8743'_786 v2
du_'8744''45'distrib'691''45''8743'_786 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'691''45''8743'_786 v0
  = let v1 = d_isBooleanAlgebra_718 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3096
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
            (coe v1)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-distribˡ-∧
d_'8744''45'distrib'737''45''8743'_788 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'737''45''8743'_788 ~v0 ~v1 v2
  = du_'8744''45'distrib'737''45''8743'_788 v2
du_'8744''45'distrib'737''45''8743'_788 ::
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'737''45''8743'_788 v0
  = let v1 = d_isBooleanAlgebra_718 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'737''45''8743'_3094
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
            (coe v1)))
-- Algebra.Lattice.Bundles.BooleanAlgebra.distributiveLattice
d_distributiveLattice_790 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 -> T_DistributiveLattice_584
d_distributiveLattice_790 ~v0 ~v1 v2
  = du_distributiveLattice_790 v2
du_distributiveLattice_790 ::
  T_BooleanAlgebra_682 -> T_DistributiveLattice_584
du_distributiveLattice_790 v0
  = coe
      C_DistributiveLattice'46'constructor_9515 (d__'8744'__708 (coe v0))
      (d__'8743'__710 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3132
         (coe d_isBooleanAlgebra_718 (coe v0)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._._≉_
d__'8777'__794 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 -> AgdaAny -> AgdaAny -> ()
d__'8777'__794 = erased
-- Algebra.Lattice.Bundles.BooleanAlgebra._.lattice
d_lattice_796 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 -> T_Lattice_500
d_lattice_796 ~v0 ~v1 v2 = du_lattice_796 v2
du_lattice_796 :: T_BooleanAlgebra_682 -> T_Lattice_500
du_lattice_796 v0
  = coe du_lattice_664 (coe du_distributiveLattice_790 (coe v0))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.rawLattice
d_rawLattice_798 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
d_rawLattice_798 ~v0 ~v1 v2 = du_rawLattice_798 v2
du_rawLattice_798 ::
  T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
du_rawLattice_798 v0
  = let v1 = coe du_distributiveLattice_790 (coe v0) in
    coe (coe du_rawLattice_566 (coe du_lattice_664 (coe v1)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.setoid
d_setoid_800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_800 ~v0 ~v1 v2 = du_setoid_800 v2
du_setoid_800 ::
  T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_800 v0
  = let v1 = coe du_distributiveLattice_790 (coe v0) in
    coe (coe du_setoid_574 (coe du_lattice_664 (coe v1)))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∧-rawMagma
d_'8743''45'rawMagma_802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'8743''45'rawMagma_802 ~v0 ~v1 v2 = du_'8743''45'rawMagma_802 v2
du_'8743''45'rawMagma_802 ::
  T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_'8743''45'rawMagma_802 v0
  = let v1 = coe du_distributiveLattice_790 (coe v0) in
    coe
      (let v2 = coe du_lattice_664 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
            (coe du_rawLattice_566 (coe v2))))
-- Algebra.Lattice.Bundles.BooleanAlgebra._.∨-rawMagma
d_'8744''45'rawMagma_804 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'8744''45'rawMagma_804 ~v0 ~v1 v2 = du_'8744''45'rawMagma_804 v2
du_'8744''45'rawMagma_804 ::
  T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_'8744''45'rawMagma_804 v0
  = let v1 = coe du_distributiveLattice_790 (coe v0) in
    coe
      (let v2 = coe du_lattice_664 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
            (coe du_rawLattice_566 (coe v2))))
