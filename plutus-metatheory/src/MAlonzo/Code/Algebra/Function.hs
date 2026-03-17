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

module MAlonzo.Code.Algebra.Function where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Function.Indexed.Relation.Binary.Equality
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Function.B._∧_
d__'8743'__16 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__16 v0
  = coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 (coe v0)
-- Algebra.Function.B._∨_
d__'8744'__18 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__18 v0
  = coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 (coe v0)
-- Algebra.Function.B._≈_
d__'8776'__20 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__20 = erased
-- Algebra.Function.B._≉_
d__'8777'__22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__22 = erased
-- Algebra.Function.B.Carrier
d_Carrier_24 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 -> ()
d_Carrier_24 = erased
-- Algebra.Function.B.absorptive
d_absorptive_26 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_26 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3020
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
               (coe v0))))
-- Algebra.Function.B.distributiveLattice
d_distributiveLattice_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
d_distributiveLattice_28 ~v0 ~v1 ~v2 ~v3 v4
  = du_distributiveLattice_28 v4
du_distributiveLattice_28 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
du_distributiveLattice_28 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
      (coe v0)
-- Algebra.Function.B.isBooleanAlgebra
d_isBooleanAlgebra_30 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3134
d_isBooleanAlgebra_30 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
      (coe v0)
-- Algebra.Function.B.isDistributiveLattice
d_isDistributiveLattice_32 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
d_isDistributiveLattice_32 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
         (coe v0))
-- Algebra.Function.B.isEquivalence
d_isEquivalence_34 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_34 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
               (coe v0))))
-- Algebra.Function.B.isLattice
d_isLattice_36 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
d_isLattice_36 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
            (coe v0)))
-- Algebra.Function.B.isPartialEquivalence
d_isPartialEquivalence_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_38 ~v0 ~v1 ~v2 ~v3 v4
  = du_isPartialEquivalence_38 v4
du_isPartialEquivalence_38 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_38 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                  (coe v3)))))
-- Algebra.Function.B.lattice
d_lattice_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
d_lattice_40 ~v0 ~v1 ~v2 ~v3 v4 = du_lattice_40 v4
du_lattice_40 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
du_lattice_40 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
         (coe v0))
-- Algebra.Function.B.rawLattice
d_rawLattice_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
d_rawLattice_42 ~v0 ~v1 ~v2 ~v3 v4 = du_rawLattice_42 v4
du_rawLattice_42 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
du_rawLattice_42 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.du_rawLattice_566
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Function.B.refl
d_refl_44 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_refl_44 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
-- Algebra.Function.B.reflexive
d_reflexive_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_46 ~v0 ~v1 ~v2 ~v3 v4 = du_reflexive_46 v4
du_reflexive_46 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_46 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
                    (coe v2) in
          coe
            (\ v4 v5 v6 ->
               coe
                 MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                    (coe v3))
                 v4)))
-- Algebra.Function.B.setoid
d_setoid_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_48 ~v0 ~v1 ~v2 ~v3 v4 = du_setoid_48 v4
du_setoid_48 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_48 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))
-- Algebra.Function.B.sym
d_sym_50 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_50 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
-- Algebra.Function.B.trans
d_trans_52 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_52 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                  (coe v0)))))
-- Algebra.Function.B.¬_
d_'172'__54 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'172'__54 v0
  = coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 (coe v0)
-- Algebra.Function.B.¬-cong
d_'172''45'cong_56 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'172''45'cong_56 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3160
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
         (coe v0))
-- Algebra.Function.B.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'absorbs'45''8744'_58 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8743''45'absorbs'45''8744'_58 v4
du_'8743''45'absorbs'45''8744'_58 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'absorbs'45''8744'_58 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3036
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
               (coe v2))))
-- Algebra.Function.B.∧-assoc
d_'8743''45'assoc_60 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_60 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3016
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
               (coe v0))))
-- Algebra.Function.B.∧-comm
d_'8743''45'comm_62 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_62 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3014
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
               (coe v0))))
-- Algebra.Function.B.∧-complement
d_'8743''45'complement_64 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'complement_64 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'complement_3158
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
         (coe v0))
-- Algebra.Function.B.∧-complementʳ
d_'8743''45'complement'691'_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8743''45'complement'691'_66 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8743''45'complement'691'_66 v4
du_'8743''45'complement'691'_66 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8743''45'complement'691'_66 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'691'_3222
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
         (coe v0))
-- Algebra.Function.B.∧-complementˡ
d_'8743''45'complement'737'_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8743''45'complement'737'_68 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8743''45'complement'737'_68 v4
du_'8743''45'complement'737'_68 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8743''45'complement'737'_68 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'complement'737'_3220
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
         (coe v0))
-- Algebra.Function.B.∧-cong
d_'8743''45'cong_70 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_70 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3018
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
               (coe v0))))
-- Algebra.Function.B.∧-congʳ
d_'8743''45'cong'691'_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'691'_72 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8743''45'cong'691'_72 v4
du_'8743''45'cong'691'_72 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'691'_72 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'691'_3042
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
               (coe v2))))
-- Algebra.Function.B.∧-congˡ
d_'8743''45'cong'737'_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong'737'_74 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8743''45'cong'737'_74 v4
du_'8743''45'cong'737'_74 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'cong'737'_74 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3038
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
               (coe v2))))
-- Algebra.Function.B.∧-distrib-∨
d_'8743''45'distrib'45''8744'_76 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_76 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3074
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
            (coe v0)))
-- Algebra.Function.B.∧-distribʳ-∨
d_'8743''45'distrib'691''45''8744'_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'691''45''8744'_78 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8743''45'distrib'691''45''8744'_78 v4
du_'8743''45'distrib'691''45''8744'_78 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'691''45''8744'_78 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'691''45''8744'_3122
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
            (coe v1)))
-- Algebra.Function.B.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'distrib'737''45''8744'_80 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8743''45'distrib'737''45''8744'_80 v4
du_'8743''45'distrib'737''45''8744'_80 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8743''45'distrib'737''45''8744'_80 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'distrib'737''45''8744'_3120
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
            (coe v1)))
-- Algebra.Function.B.∧-rawMagma
d_'8743''45'rawMagma_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42
d_'8743''45'rawMagma_82 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8743''45'rawMagma_82 v4
du_'8743''45'rawMagma_82 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42
du_'8743''45'rawMagma_82 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_rawLattice_566 (coe v2))))
-- Algebra.Function.B.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'absorbs'45''8743'_84 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8744''45'absorbs'45''8743'_84 v4
du_'8744''45'absorbs'45''8743'_84 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'absorbs'45''8743'_84 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3034
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
               (coe v2))))
-- Algebra.Function.B.∨-assoc
d_'8744''45'assoc_86 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_86 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3010
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
               (coe v0))))
-- Algebra.Function.B.∨-comm
d_'8744''45'comm_88 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_88 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3008
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
               (coe v0))))
-- Algebra.Function.B.∨-complement
d_'8744''45'complement_90 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'complement_90 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'complement_3156
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
         (coe v0))
-- Algebra.Function.B.∨-complementʳ
d_'8744''45'complement'691'_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8744''45'complement'691'_92 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8744''45'complement'691'_92 v4
du_'8744''45'complement'691'_92 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8744''45'complement'691'_92 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'691'_3218
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
         (coe v0))
-- Algebra.Function.B.∨-complementˡ
d_'8744''45'complement'737'_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8744''45'complement'737'_94 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8744''45'complement'737'_94 v4
du_'8744''45'complement'737'_94 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
du_'8744''45'complement'737'_94 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'complement'737'_3216
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
         (coe v0))
-- Algebra.Function.B.∨-cong
d_'8744''45'cong_96 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_96 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3012
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
               (coe v0))))
-- Algebra.Function.B.∨-congʳ
d_'8744''45'cong'691'_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'691'_98 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8744''45'cong'691'_98 v4
du_'8744''45'cong'691'_98 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'691'_98 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'691'_3050
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
               (coe v2))))
-- Algebra.Function.B.∨-congˡ
d_'8744''45'cong'737'_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong'737'_100 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8744''45'cong'737'_100 v4
du_'8744''45'cong'737'_100 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'cong'737'_100 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
              (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3046
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
               (coe v2))))
-- Algebra.Function.B.∨-distrib-∧
d_'8744''45'distrib'45''8743'_102 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_102 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3072
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
            (coe v0)))
-- Algebra.Function.B.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'691''45''8743'_104 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8744''45'distrib'691''45''8743'_104 v4
du_'8744''45'distrib'691''45''8743'_104 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'691''45''8743'_104 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'691''45''8743'_3118
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
            (coe v1)))
-- Algebra.Function.B.∨-distribˡ-∧
d_'8744''45'distrib'737''45''8743'_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'distrib'737''45''8743'_106 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8744''45'distrib'737''45''8743'_106 v4
du_'8744''45'distrib'737''45''8743'_106 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8744''45'distrib'737''45''8743'_106 v0
  = let v1
          = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'distrib'737''45''8743'_3116
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
            (coe v1)))
-- Algebra.Function.B.∨-rawMagma
d_'8744''45'rawMagma_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42
d_'8744''45'rawMagma_108 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8744''45'rawMagma_108 v4
du_'8744''45'rawMagma_108 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42
du_'8744''45'rawMagma_108 v0
  = let v1
          = coe
              MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
              (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_rawLattice_566 (coe v2))))
-- Algebra.Function.B.⊤
d_'8868'_110 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny
d_'8868'_110 v0
  = coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)
-- Algebra.Function.B.⊥
d_'8869'_112 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny
d_'8869'_112 v0
  = coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)
-- Algebra.Function.Carrier
d_Carrier_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 -> ()
d_Carrier_114 = erased
-- Algebra.Function._≈_
d__'8776'__116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d__'8776'__116 = erased
-- Algebra.Function._∨_
d__'8744'__124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'8744'__124 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du__'8744'__124 v4 v5 v6 v7
du__'8744'__124 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'8744'__124 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708 v0 (coe v1 v3)
      (coe v2 v3)
-- Algebra.Function._∧_
d__'8743'__132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'8743'__132 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du__'8743'__132 v4 v5 v6 v7
du__'8743'__132 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'8743'__132 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710 v0 (coe v1 v3)
      (coe v2 v3)
-- Algebra.Function.¬_
d_'172'__140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'172'__140 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_'172'__140 v4 v5 v6
du_'172'__140 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'172'__140 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712 v0 (coe v1 v2)
-- Algebra.Function.⊤
d_'8868'_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8868'_146 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_'8868'_146 v4
du_'8868'_146 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny
du_'8868'_146 v0
  = coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714 (coe v0)
-- Algebra.Function.⊥
d_'8869'_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny -> AgdaAny
d_'8869'_150 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_'8869'_150 v4
du_'8869'_150 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  AgdaAny
du_'8869'_150 v0
  = coe MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716 (coe v0)
-- Algebra.Function.isLattice'
d_isLattice''_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
d_isLattice''_154 ~v0 ~v1 ~v2 ~v3 v4 = du_isLattice''_154 v4
du_isLattice''_154 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
du_isLattice''_154 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_IsLattice'46'constructor_36909
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
         (coe
            MAlonzo.Code.Function.Indexed.Relation.Binary.Equality.du_'8801''45'setoid_18
            (coe
               MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial.du_indexedSetoid_106
               (let v1
                      = coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                          (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1)))))))
      (coe
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3008
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0))))
              (coe v1 v3) (coe v2 v3)))
      (coe
         (\ v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3010
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0))))
              (coe v1 v4) (coe v2 v4) (coe v3 v4)))
      (coe
         (\ v1 v2 v3 v4 v5 v6 v7 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3012
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0))))
              (coe v1 v7) (coe v2 v7) (coe v3 v7) (coe v4 v7) (coe v5 v7)
              (coe v6 v7)))
      (coe
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3014
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0))))
              (coe v1 v3) (coe v2 v3)))
      (coe
         (\ v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3016
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0))))
              (coe v1 v4) (coe v2 v4) (coe v3 v4)))
      (coe
         (\ v1 v2 v3 v4 v5 v6 v7 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3018
              (MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
                 (coe
                    MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0))))
              (coe v1 v7) (coe v2 v7) (coe v3 v7) (coe v4 v7) (coe v5 v7)
              (coe v6 v7)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v1 v2 v3 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3020
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                          (coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                             (coe v0)))))
                 (coe v1 v3) (coe v2 v3)))
         (coe
            (\ v1 v2 v3 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3020
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                          (coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                             (coe v0)))))
                 (coe v1 v3) (coe v2 v3))))
-- Algebra.Function.isDistributiveLattice'
d_isDistributiveLattice''_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
d_isDistributiveLattice''_208 ~v0 ~v1 ~v2 ~v3 v4
  = du_isDistributiveLattice''_208 v4
du_isDistributiveLattice''_208 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
du_isDistributiveLattice''_208 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_IsDistributiveLattice'46'constructor_41059
      (coe du_isLattice''_154 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v1 v2 v3 v4 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3072
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0))))
                 (coe v1 v4) (coe v2 v4) (coe v3 v4)))
         (coe
            (\ v1 v2 v3 v4 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3072
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0))))
                 (coe v1 v4) (coe v2 v4) (coe v3 v4))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v1 v2 v3 v4 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3074
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0))))
                 (coe v1 v4) (coe v2 v4) (coe v3 v4)))
         (coe
            (\ v1 v2 v3 v4 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3074
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                          (coe v0))))
                 (coe v1 v4) (coe v2 v4) (coe v3 v4))))
-- Algebra.Function.isBooleanAlgebra
d_isBooleanAlgebra_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3134
d_isBooleanAlgebra_242 ~v0 ~v1 ~v2 ~v3 v4
  = du_isBooleanAlgebra_242 v4
du_isBooleanAlgebra_242 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3134
du_isBooleanAlgebra_242 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_IsBooleanAlgebra'46'constructor_44131
      (coe du_isDistributiveLattice''_208 (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'complement_3156
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0)))
                 (coe v1 v2)))
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'complement_3156
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0)))
                 (coe v1 v2))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'complement_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0)))
                 (coe v1 v2)))
         (coe
            (\ v1 v2 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'complement_3158
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                       (coe v0)))
                 (coe v1 v2))))
      (coe
         (\ v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Algebra.Lattice.Structures.d_'172''45'cong_3160
              (MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                 (coe v0))
              (coe v1 v4) (coe v2 v4) (coe v3 v4)))
-- Algebra.Function.hom
d_hom_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682
d_hom_264 ~v0 ~v1 ~v2 ~v3 v4 = du_hom_264 v4
du_hom_264 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682
du_hom_264 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_BooleanAlgebra'46'constructor_11509
      (coe du__'8744'__124 (coe v0)) (coe du__'8743'__132 (coe v0))
      (coe du_'172'__140 (coe v0)) (\ v1 -> coe du_'8868'_146 (coe v0))
      (\ v1 -> coe du_'8869'_150 (coe v0))
      (coe du_isBooleanAlgebra_242 (coe v0))
