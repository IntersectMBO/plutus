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

module MAlonzo.Code.Algebra.Lattice.Properties.Lattice where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Lattice.Bundles qualified
import MAlonzo.Code.Algebra.Lattice.Properties.Semilattice qualified
import MAlonzo.Code.Algebra.Lattice.Structures qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Construct.NaturalOrder.Left qualified
import MAlonzo.Code.Relation.Binary.Lattice.Bundles qualified
import MAlonzo.Code.Relation.Binary.Lattice.Structures qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Base.Single qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Syntax qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Lattice.Properties.Lattice._.Idempotent
d_Idempotent_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Idempotent_112 = erased
-- Algebra.Lattice.Properties.Lattice._.IsBand
d_IsBand_210 a0 a1 a2 a3 = ()
-- Algebra.Lattice.Properties.Lattice._.IsMagma
d_IsMagma_250 a0 a1 a2 a3 = ()
-- Algebra.Lattice.Properties.Lattice._.IsSemigroup
d_IsSemigroup_278 a0 a1 a2 a3 = ()
-- Algebra.Lattice.Properties.Lattice._.IsBand.idem
d_idem_392 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508 -> AgdaAny -> AgdaAny
d_idem_392 v0
  = coe MAlonzo.Code.Algebra.Structures.d_idem_518 (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsBand.isSemigroup
d_isSemigroup_400 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_508 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_400 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_516 (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsMagma.isEquivalence
d_isEquivalence_1550 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1550 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsMagma.∙-cong
d_'8729''45'cong_1564 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1564 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsSemigroup.assoc
d_assoc_2404 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2404 v0
  = coe MAlonzo.Code.Algebra.Structures.d_assoc_482 (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsSemigroup.isMagma
d_isMagma_2408 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2408 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice
d_IsLattice_2732 a0 a1 a2 a3 a4 = ()
-- Algebra.Lattice.Properties.Lattice._.IsSemilattice
d_IsSemilattice_2736 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_IsSemilattice_2736 = erased
-- Algebra.Lattice.Properties.Lattice._.IsLattice.absorptive
d_absorptive_3036 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_3036 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_2998 (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice.isEquivalence
d_isEquivalence_3038 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_3038 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
      (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice.∧-assoc
d_'8743''45'assoc_3052 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_3052 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
      (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice.∧-comm
d_'8743''45'comm_3054 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_3054 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
      (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice.∧-cong
d_'8743''45'cong_3056 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_3056 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
      (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice.∨-assoc
d_'8744''45'assoc_3064 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_3064 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_2988
      (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice.∨-comm
d_'8744''45'comm_3066 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_3066 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
      (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice.∨-cong
d_'8744''45'cong_3068 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_3068 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
      (coe v0)
-- Algebra.Lattice.Properties.Lattice.∧-idem
d_'8743''45'idem_3182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  AgdaAny -> AgdaAny
d_'8743''45'idem_3182 ~v0 ~v1 v2 v3 = du_'8743''45'idem_3182 v2 v3
du_'8743''45'idem_3182 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  AgdaAny -> AgdaAny
du_'8743''45'idem_3182 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v1)
      v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0))))
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v1)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v1)))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v1)))
            v1 v1
            (let v2
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                          (coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v2))
                  (coe v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3014
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)) v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v1)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0))
            (coe v1)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v1))
            (coe v1)
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3012
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)) v1
               v1)))
-- Algebra.Lattice.Properties.Lattice.∧-isMagma
d_'8743''45'isMagma_3186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8743''45'isMagma_3186 ~v0 ~v1 v2 = du_'8743''45'isMagma_3186 v2
du_'8743''45'isMagma_3186 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'8743''45'isMagma_3186 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
-- Algebra.Lattice.Properties.Lattice.∧-isSemigroup
d_'8743''45'isSemigroup_3188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8743''45'isSemigroup_3188 ~v0 ~v1 v2
  = du_'8743''45'isSemigroup_3188 v2
du_'8743''45'isSemigroup_3188 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'8743''45'isSemigroup_3188 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10417
      (coe du_'8743''45'isMagma_3186 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
-- Algebra.Lattice.Properties.Lattice.∧-isBand
d_'8743''45'isBand_3190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8743''45'isBand_3190 ~v0 ~v1 v2 = du_'8743''45'isBand_3190 v2
du_'8743''45'isBand_3190 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_'8743''45'isBand_3190 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsBand'46'constructor_11205
      (coe du_'8743''45'isSemigroup_3188 (coe v0))
      (coe du_'8743''45'idem_3182 (coe v0))
-- Algebra.Lattice.Properties.Lattice.∧-isSemilattice
d_'8743''45'isSemilattice_3192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_'8743''45'isSemilattice_3192 ~v0 ~v1 v2
  = du_'8743''45'isSemilattice_3192 v2
du_'8743''45'isSemilattice_3192 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
du_'8743''45'isSemilattice_3192 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeBand'46'constructor_13109
      (coe du_'8743''45'isBand_3190 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
-- Algebra.Lattice.Properties.Lattice.∧-semilattice
d_'8743''45'semilattice_3194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8743''45'semilattice_3194 ~v0 ~v1 v2
  = du_'8743''45'semilattice_3194 v2
du_'8743''45'semilattice_3194 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
du_'8743''45'semilattice_3194 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_Semilattice'46'constructor_193
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 (coe v0))
      (coe du_'8743''45'isSemilattice_3192 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-isOrderTheoreticJoinSemilattice
d_'8743''45'isOrderTheoreticJoinSemilattice_3198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_'8743''45'isOrderTheoreticJoinSemilattice_3198 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticJoinSemilattice_3198 v2
du_'8743''45'isOrderTheoreticJoinSemilattice_3198 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_'8743''45'isOrderTheoreticJoinSemilattice_3198 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
      (coe du_'8743''45'semilattice_3194 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-isOrderTheoreticMeetSemilattice
d_'8743''45'isOrderTheoreticMeetSemilattice_3200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
d_'8743''45'isOrderTheoreticMeetSemilattice_3200 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticMeetSemilattice_3200 v2
du_'8743''45'isOrderTheoreticMeetSemilattice_3200 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
du_'8743''45'isOrderTheoreticMeetSemilattice_3200 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticMeetSemilattice_176
      (coe du_'8743''45'semilattice_3194 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-orderTheoreticJoinSemilattice
d_'8743''45'orderTheoreticJoinSemilattice_3202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
d_'8743''45'orderTheoreticJoinSemilattice_3202 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticJoinSemilattice_3202 v2
du_'8743''45'orderTheoreticJoinSemilattice_3202 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
du_'8743''45'orderTheoreticJoinSemilattice_3202 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticJoinSemilattice_182
      (coe du_'8743''45'semilattice_3194 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-orderTheoreticMeetSemilattice
d_'8743''45'orderTheoreticMeetSemilattice_3204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_200
d_'8743''45'orderTheoreticMeetSemilattice_3204 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticMeetSemilattice_3204 v2
du_'8743''45'orderTheoreticMeetSemilattice_3204 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_200
du_'8743''45'orderTheoreticMeetSemilattice_3204 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticMeetSemilattice_180
      (coe du_'8743''45'semilattice_3194 (coe v0))
-- Algebra.Lattice.Properties.Lattice.∨-idem
d_'8744''45'idem_3206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  AgdaAny -> AgdaAny
d_'8744''45'idem_3206 ~v0 ~v1 v2 v3 = du_'8744''45'idem_3206 v2 v3
du_'8744''45'idem_3206 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  AgdaAny -> AgdaAny
du_'8744''45'idem_3206 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v1 v1)
      v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0))))
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v1 v1)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v1))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v1))
            v1 v1
            (let v2
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                          (coe
                             MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v2))
                  (coe v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3012
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)) v1
               v1))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3024
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0))
            (coe v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v1)
            (coe v1) (coe du_'8743''45'idem_3182 (coe v0) (coe v1))))
-- Algebra.Lattice.Properties.Lattice.∨-isMagma
d_'8744''45'isMagma_3210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8744''45'isMagma_3210 ~v0 ~v1 v2 = du_'8744''45'isMagma_3210 v2
du_'8744''45'isMagma_3210 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'8744''45'isMagma_3210 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
-- Algebra.Lattice.Properties.Lattice.∨-isSemigroup
d_'8744''45'isSemigroup_3212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'8744''45'isSemigroup_3212 ~v0 ~v1 v2
  = du_'8744''45'isSemigroup_3212 v2
du_'8744''45'isSemigroup_3212 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'8744''45'isSemigroup_3212 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10417
      (coe du_'8744''45'isMagma_3210 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_2988
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
-- Algebra.Lattice.Properties.Lattice.∨-isBand
d_'8744''45'isBand_3214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
d_'8744''45'isBand_3214 ~v0 ~v1 v2 = du_'8744''45'isBand_3214 v2
du_'8744''45'isBand_3214 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_508
du_'8744''45'isBand_3214 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsBand'46'constructor_11205
      (coe du_'8744''45'isSemigroup_3212 (coe v0))
      (coe du_'8744''45'idem_3206 (coe v0))
-- Algebra.Lattice.Properties.Lattice.∨-isSemilattice
d_'8744''45'isSemilattice_3216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
d_'8744''45'isSemilattice_3216 ~v0 ~v1 v2
  = du_'8744''45'isSemilattice_3216 v2
du_'8744''45'isSemilattice_3216 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_590
du_'8744''45'isSemilattice_3216 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeBand'46'constructor_13109
      (coe du_'8744''45'isBand_3214 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
-- Algebra.Lattice.Properties.Lattice.∨-semilattice
d_'8744''45'semilattice_3218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8744''45'semilattice_3218 ~v0 ~v1 v2
  = du_'8744''45'semilattice_3218 v2
du_'8744''45'semilattice_3218 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
du_'8744''45'semilattice_3218 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_Semilattice'46'constructor_193
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 (coe v0))
      (coe du_'8744''45'isSemilattice_3216 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-isOrderTheoreticJoinSemilattice
d_'8743''45'isOrderTheoreticJoinSemilattice_3222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_'8743''45'isOrderTheoreticJoinSemilattice_3222 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticJoinSemilattice_3222 v2
du_'8743''45'isOrderTheoreticJoinSemilattice_3222 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_'8743''45'isOrderTheoreticJoinSemilattice_3222 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
      (coe du_'8744''45'semilattice_3218 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-isOrderTheoreticMeetSemilattice
d_'8743''45'isOrderTheoreticMeetSemilattice_3224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
d_'8743''45'isOrderTheoreticMeetSemilattice_3224 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticMeetSemilattice_3224 v2
du_'8743''45'isOrderTheoreticMeetSemilattice_3224 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_180
du_'8743''45'isOrderTheoreticMeetSemilattice_3224 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticMeetSemilattice_176
      (coe du_'8744''45'semilattice_3218 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-orderTheoreticJoinSemilattice
d_'8743''45'orderTheoreticJoinSemilattice_3226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
d_'8743''45'orderTheoreticJoinSemilattice_3226 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticJoinSemilattice_3226 v2
du_'8743''45'orderTheoreticJoinSemilattice_3226 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
du_'8743''45'orderTheoreticJoinSemilattice_3226 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticJoinSemilattice_182
      (coe du_'8744''45'semilattice_3218 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-orderTheoreticMeetSemilattice
d_'8743''45'orderTheoreticMeetSemilattice_3228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_200
d_'8743''45'orderTheoreticMeetSemilattice_3228 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticMeetSemilattice_3228 v2
du_'8743''45'orderTheoreticMeetSemilattice_3228 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_200
du_'8743''45'orderTheoreticMeetSemilattice_3228 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticMeetSemilattice_180
      (coe du_'8744''45'semilattice_3218 (coe v0))
-- Algebra.Lattice.Properties.Lattice.∧-∨-isLattice
d_'8743''45''8744''45'isLattice_3230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
d_'8743''45''8744''45'isLattice_3230 ~v0 ~v1 v2
  = du_'8743''45''8744''45'isLattice_3230 v2
du_'8743''45''8744''45'isLattice_3230 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2962
du_'8743''45''8744''45'isLattice_3230 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_IsLattice'46'constructor_36793
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_2994
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_2996
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_2988
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_2990
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
      (coe
         MAlonzo.Code.Data.Product.Base.du_swap_370
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_2998
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0))))
-- Algebra.Lattice.Properties.Lattice.∧-∨-lattice
d_'8743''45''8744''45'lattice_3232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
d_'8743''45''8744''45'lattice_3232 ~v0 ~v1 v2
  = du_'8743''45''8744''45'lattice_3232 v2
du_'8743''45''8744''45'lattice_3232 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
du_'8743''45''8744''45'lattice_3232 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_Lattice'46'constructor_7925
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 (coe v0))
      (coe du_'8743''45''8744''45'isLattice_3230 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.poset
d_poset_3236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_3236 ~v0 ~v1 v2 = du_poset_3236 v2
du_poset_3236 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_3236 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_poset_162
      (coe du_'8743''45'semilattice_3194 (coe v0))
-- Algebra.Lattice.Properties.Lattice._._≤_
d__'8804'__3240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  AgdaAny -> AgdaAny -> ()
d__'8804'__3240 = erased
-- Algebra.Lattice.Properties.Lattice.∨-∧-isOrderTheoreticLattice
d_'8744''45''8743''45'isOrderTheoreticLattice_3244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
d_'8744''45''8743''45'isOrderTheoreticLattice_3244 ~v0 ~v1 v2
  = du_'8744''45''8743''45'isOrderTheoreticLattice_3244 v2
du_'8744''45''8743''45'isOrderTheoreticLattice_3244 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_340
du_'8744''45''8743''45'isOrderTheoreticLattice_3244 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.C_IsLattice'46'constructor_14941
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_poset_162
            (coe du_'8743''45'semilattice_3194 (coe v0))))
      (coe du_supremum_3288 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.NaturalOrder.Left.du_infimum_3640
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 (coe v0))
         (coe du_'8743''45'isSemilattice_3192 (coe v0)))
-- Algebra.Lattice.Properties.Lattice._._._≤_
d__'8804'__3256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  AgdaAny -> AgdaAny -> ()
d__'8804'__3256 = erased
-- Algebra.Lattice.Properties.Lattice._.sound
d_sound_3268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sound_3268 ~v0 ~v1 v2 v3 v4 v5 = du_sound_3268 v2 v3 v4 v5
du_sound_3268 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sound_3268 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v2)
      v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v4 v5 v6 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v2)
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v2 v1))
            v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v2 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v1 v2))
               v1
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v1 v2))
                  v1 v1
                  (let v4
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524
                                   (coe v0))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v4))
                        (coe v1)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3014
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)) v1
                     v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0))
                  (coe v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v2 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v1 v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_2986
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)) v2
                     v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3016
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0))
               (coe v1) (coe v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v2 v1)
               (coe v3))))
-- Algebra.Lattice.Properties.Lattice._.complete
d_complete_3280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_complete_3280 ~v0 ~v1 v2 v3 v4 v5 = du_complete_3280 v2 v3 v4 v5
du_complete_3280 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_complete_3280 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v2 v1)
      v2
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v4 v5 v6 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v2 v1)
         v2
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v2 v1)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v2
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v2))
            v2
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v2 v1))
               v2
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v2 v1))
                  v2 v2
                  (let v4
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_2984
                                (coe
                                   MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524
                                   (coe v0))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v4))
                        (coe v2)))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3012
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)) v2
                     v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3024
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0))
                  (coe v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v2 v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_2992
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0)) v1
                     v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3024
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_524 (coe v0))
               (coe v2) (coe v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 v0 v1 v2)
               (coe v3))))
-- Algebra.Lattice.Properties.Lattice._.supremum
d_supremum_3288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_3288 ~v0 ~v1 v2 v3 v4 = du_supremum_3288 v2 v3 v4
du_supremum_3288 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_supremum_3288 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_sound_3268 (coe v0) (coe v1)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v1 v2)
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
               (coe du_'8744''45'semilattice_3218 (coe v0)))
            (coe v1) (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            du_sound_3268 (coe v0) (coe v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v1 v2)
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
               (coe
                  MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
                  (coe du_'8744''45'semilattice_3218 (coe v0)))
               (coe v1) (coe v2)))
         (coe
            (\ v3 v4 v5 ->
               coe
                 du_sound_3268 (coe v0)
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 v0 v1 v2)
                 (coe v3)
                 (coe
                    MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
                       (coe du_'8744''45'semilattice_3218 (coe v0)))
                    v1 v2 v3 (coe du_complete_3280 (coe v0) (coe v1) (coe v3) (coe v4))
                    (coe du_complete_3280 (coe v0) (coe v2) (coe v3) (coe v5))))))
-- Algebra.Lattice.Properties.Lattice.∨-∧-orderTheoreticLattice
d_'8744''45''8743''45'orderTheoreticLattice_3300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_Lattice_386
d_'8744''45''8743''45'orderTheoreticLattice_3300 ~v0 ~v1 v2
  = du_'8744''45''8743''45'orderTheoreticLattice_3300 v2
du_'8744''45''8743''45'orderTheoreticLattice_3300 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_Lattice_386
du_'8744''45''8743''45'orderTheoreticLattice_3300 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Bundles.C_Lattice'46'constructor_8977
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__520 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__522 (coe v0))
      (coe du_'8744''45''8743''45'isOrderTheoreticLattice_3244 (coe v0))
