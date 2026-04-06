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

module MAlonzo.Code.Algebra.Lattice.Properties.Lattice where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Properties.Semilattice
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.NaturalOrder.Left
import qualified MAlonzo.Code.Relation.Binary.Lattice.Bundles
import qualified MAlonzo.Code.Relation.Binary.Lattice.Structures
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Lattice.Properties.Lattice._.Idempotent
d_Idempotent_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Idempotent_78 = erased
-- Algebra.Lattice.Properties.Lattice._.IsBand
d_IsBand_82 a0 a1 a2 a3 = ()
-- Algebra.Lattice.Properties.Lattice._.IsMagma
d_IsMagma_86 a0 a1 a2 a3 = ()
-- Algebra.Lattice.Properties.Lattice._.IsSemigroup
d_IsSemigroup_90 a0 a1 a2 a3 = ()
-- Algebra.Lattice.Properties.Lattice._.IsBand.idem
d_idem_98 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 -> AgdaAny -> AgdaAny
d_idem_98 v0
  = coe MAlonzo.Code.Algebra.Structures.d_idem_536 (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsBand.isSemigroup
d_isSemigroup_106 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_106 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsMagma.isEquivalence
d_isEquivalence_126 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_126 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsMagma.∙-cong
d_'8729''45'cong_140 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_140 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsSemigroup.assoc
d_assoc_148 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_148 v0
  = coe MAlonzo.Code.Algebra.Structures.d_assoc_498 (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsSemigroup.isMagma
d_isMagma_152 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_152 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice
d_IsLattice_174 a0 a1 a2 a3 a4 = ()
-- Algebra.Lattice.Properties.Lattice._.IsSemilattice
d_IsSemilattice_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_IsSemilattice_178 = erased
-- Algebra.Lattice.Properties.Lattice._.IsLattice.absorptive
d_absorptive_182 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_182 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3106 (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice.isEquivalence
d_isEquivalence_184 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_184 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
      (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice.∧-assoc
d_'8743''45'assoc_198 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'assoc_198 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
      (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice.∧-comm
d_'8743''45'comm_200 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'comm_200 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
      (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice.∧-cong
d_'8743''45'cong_202 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8743''45'cong_202 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
      (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice.∨-assoc
d_'8744''45'assoc_210 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'assoc_210 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
      (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice.∨-comm
d_'8744''45'comm_212 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'comm_212 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
      (coe v0)
-- Algebra.Lattice.Properties.Lattice._.IsLattice.∨-cong
d_'8744''45'cong_214 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8744''45'cong_214 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
      (coe v0)
-- Algebra.Lattice.Properties.Lattice.∧-idem
d_'8743''45'idem_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  AgdaAny -> AgdaAny
d_'8743''45'idem_294 ~v0 ~v1 v2 v3 = du_'8743''45'idem_294 v2 v3
du_'8743''45'idem_294 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  AgdaAny -> AgdaAny
du_'8743''45'idem_294 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v1)
      v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0))))
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v1)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v1)))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v1
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v1)))
            v1 v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))))
               (coe v1))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3122
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)) v1
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v1)))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0))
            (coe v1)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v1))
            (coe v1)
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3120
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)) v1
               v1)))
-- Algebra.Lattice.Properties.Lattice.∧-isMagma
d_'8743''45'isMagma_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8743''45'isMagma_298 ~v0 ~v1 v2 = du_'8743''45'isMagma_298 v2
du_'8743''45'isMagma_298 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'8743''45'isMagma_298 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
-- Algebra.Lattice.Properties.Lattice.∧-isSemigroup
d_'8743''45'isSemigroup_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8743''45'isSemigroup_300 ~v0 ~v1 v2
  = du_'8743''45'isSemigroup_300 v2
du_'8743''45'isSemigroup_300 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'8743''45'isSemigroup_300 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe du_'8743''45'isMagma_298 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
-- Algebra.Lattice.Properties.Lattice.∧-isBand
d_'8743''45'isBand_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_'8743''45'isBand_302 ~v0 ~v1 v2 = du_'8743''45'isBand_302 v2
du_'8743''45'isBand_302 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_'8743''45'isBand_302 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_564
      (coe du_'8743''45'isSemigroup_300 (coe v0))
      (coe du_'8743''45'idem_294 (coe v0))
-- Algebra.Lattice.Properties.Lattice.∧-isSemilattice
d_'8743''45'isSemilattice_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_'8743''45'isSemilattice_304 ~v0 ~v1 v2
  = du_'8743''45'isSemilattice_304 v2
du_'8743''45'isSemilattice_304 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_'8743''45'isSemilattice_304 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_660
      (coe du_'8743''45'isBand_302 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
-- Algebra.Lattice.Properties.Lattice.∧-semilattice
d_'8743''45'semilattice_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8743''45'semilattice_306 ~v0 ~v1 v2
  = du_'8743''45'semilattice_306 v2
du_'8743''45'semilattice_306 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
du_'8743''45'semilattice_306 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_constructor_84
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 (coe v0))
      (coe du_'8743''45'isSemilattice_304 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-isOrderTheoreticJoinSemilattice
d_'8743''45'isOrderTheoreticJoinSemilattice_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_'8743''45'isOrderTheoreticJoinSemilattice_310 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticJoinSemilattice_310 v2
du_'8743''45'isOrderTheoreticJoinSemilattice_310 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_'8743''45'isOrderTheoreticJoinSemilattice_310 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
      (coe du_'8743''45'semilattice_306 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-isOrderTheoreticMeetSemilattice
d_'8743''45'isOrderTheoreticMeetSemilattice_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
d_'8743''45'isOrderTheoreticMeetSemilattice_312 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticMeetSemilattice_312 v2
du_'8743''45'isOrderTheoreticMeetSemilattice_312 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
du_'8743''45'isOrderTheoreticMeetSemilattice_312 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticMeetSemilattice_176
      (coe du_'8743''45'semilattice_306 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-orderTheoreticJoinSemilattice
d_'8743''45'orderTheoreticJoinSemilattice_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
d_'8743''45'orderTheoreticJoinSemilattice_314 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticJoinSemilattice_314 v2
du_'8743''45'orderTheoreticJoinSemilattice_314 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
du_'8743''45'orderTheoreticJoinSemilattice_314 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticJoinSemilattice_182
      (coe du_'8743''45'semilattice_306 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-orderTheoreticMeetSemilattice
d_'8743''45'orderTheoreticMeetSemilattice_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_204
d_'8743''45'orderTheoreticMeetSemilattice_316 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticMeetSemilattice_316 v2
du_'8743''45'orderTheoreticMeetSemilattice_316 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_204
du_'8743''45'orderTheoreticMeetSemilattice_316 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticMeetSemilattice_180
      (coe du_'8743''45'semilattice_306 (coe v0))
-- Algebra.Lattice.Properties.Lattice.∨-idem
d_'8744''45'idem_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  AgdaAny -> AgdaAny
d_'8744''45'idem_318 ~v0 ~v1 v2 v3 = du_'8744''45'idem_318 v2 v3
du_'8744''45'idem_318 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  AgdaAny -> AgdaAny
du_'8744''45'idem_318 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v1 v1)
      v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_40
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0))))
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v1 v1)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v1
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v1))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))))
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v1))
            v1 v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))))
               (coe v1))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3120
               (MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)) v1
               v1))
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3132
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0))
            (coe v1)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v1)
            (coe v1) (coe du_'8743''45'idem_294 (coe v0) (coe v1))))
-- Algebra.Lattice.Properties.Lattice.∨-isMagma
d_'8744''45'isMagma_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8744''45'isMagma_322 ~v0 ~v1 v2 = du_'8744''45'isMagma_322 v2
du_'8744''45'isMagma_322 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'8744''45'isMagma_322 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
-- Algebra.Lattice.Properties.Lattice.∨-isSemigroup
d_'8744''45'isSemigroup_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8744''45'isSemigroup_324 ~v0 ~v1 v2
  = du_'8744''45'isSemigroup_324 v2
du_'8744''45'isSemigroup_324 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'8744''45'isSemigroup_324 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe du_'8744''45'isMagma_322 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
-- Algebra.Lattice.Properties.Lattice.∨-isBand
d_'8744''45'isBand_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_'8744''45'isBand_326 ~v0 ~v1 v2 = du_'8744''45'isBand_326 v2
du_'8744''45'isBand_326 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_'8744''45'isBand_326 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_564
      (coe du_'8744''45'isSemigroup_324 (coe v0))
      (coe du_'8744''45'idem_318 (coe v0))
-- Algebra.Lattice.Properties.Lattice.∨-isSemilattice
d_'8744''45'isSemilattice_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
d_'8744''45'isSemilattice_328 ~v0 ~v1 v2
  = du_'8744''45'isSemilattice_328 v2
du_'8744''45'isSemilattice_328 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_612
du_'8744''45'isSemilattice_328 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_660
      (coe du_'8744''45'isBand_326 (coe v0))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
-- Algebra.Lattice.Properties.Lattice.∨-semilattice
d_'8744''45'semilattice_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8744''45'semilattice_330 ~v0 ~v1 v2
  = du_'8744''45'semilattice_330 v2
du_'8744''45'semilattice_330 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
du_'8744''45'semilattice_330 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_constructor_84
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 (coe v0))
      (coe du_'8744''45'isSemilattice_328 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-isOrderTheoreticJoinSemilattice
d_'8743''45'isOrderTheoreticJoinSemilattice_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
d_'8743''45'isOrderTheoreticJoinSemilattice_334 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticJoinSemilattice_334 v2
du_'8743''45'isOrderTheoreticJoinSemilattice_334 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsJoinSemilattice_22
du_'8743''45'isOrderTheoreticJoinSemilattice_334 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
      (coe du_'8744''45'semilattice_330 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-isOrderTheoreticMeetSemilattice
d_'8743''45'isOrderTheoreticMeetSemilattice_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
d_'8743''45'isOrderTheoreticMeetSemilattice_336 ~v0 ~v1 v2
  = du_'8743''45'isOrderTheoreticMeetSemilattice_336 v2
du_'8743''45'isOrderTheoreticMeetSemilattice_336 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsMeetSemilattice_184
du_'8743''45'isOrderTheoreticMeetSemilattice_336 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticMeetSemilattice_176
      (coe du_'8744''45'semilattice_330 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-orderTheoreticJoinSemilattice
d_'8743''45'orderTheoreticJoinSemilattice_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
d_'8743''45'orderTheoreticJoinSemilattice_338 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticJoinSemilattice_338 v2
du_'8743''45'orderTheoreticJoinSemilattice_338 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_JoinSemilattice_14
du_'8743''45'orderTheoreticJoinSemilattice_338 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticJoinSemilattice_182
      (coe du_'8744''45'semilattice_330 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.∧-orderTheoreticMeetSemilattice
d_'8743''45'orderTheoreticMeetSemilattice_340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_204
d_'8743''45'orderTheoreticMeetSemilattice_340 ~v0 ~v1 v2
  = du_'8743''45'orderTheoreticMeetSemilattice_340 v2
du_'8743''45'orderTheoreticMeetSemilattice_340 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_MeetSemilattice_204
du_'8743''45'orderTheoreticMeetSemilattice_340 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'orderTheoreticMeetSemilattice_180
      (coe du_'8744''45'semilattice_330 (coe v0))
-- Algebra.Lattice.Properties.Lattice.∧-∨-isLattice
d_'8743''45''8744''45'isLattice_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
d_'8743''45''8744''45'isLattice_342 ~v0 ~v1 v2
  = du_'8743''45''8744''45'isLattice_342 v2
du_'8743''45''8744''45'isLattice_342 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_3070
du_'8743''45''8744''45'isLattice_342 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.C_constructor_3140
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'assoc_3102
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'cong_3104
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'assoc_3096
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'cong_3098
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
      (coe
         MAlonzo.Code.Data.Product.Base.du_swap_370
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3106
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0))))
-- Algebra.Lattice.Properties.Lattice.∧-∨-lattice
d_'8743''45''8744''45'lattice_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512
d_'8743''45''8744''45'lattice_344 ~v0 ~v1 v2
  = du_'8743''45''8744''45'lattice_344 v2
du_'8743''45''8744''45'lattice_344 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512
du_'8743''45''8744''45'lattice_344 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.C_constructor_592
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 (coe v0))
      (coe du_'8743''45''8744''45'isLattice_342 (coe v0))
-- Algebra.Lattice.Properties.Lattice._.poset
d_poset_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_348 ~v0 ~v1 v2 = du_poset_348 v2
du_poset_348 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_348 v0
  = coe
      MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_poset_162
      (coe du_'8743''45'semilattice_306 (coe v0))
-- Algebra.Lattice.Properties.Lattice._._≤_
d__'8804'__352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  AgdaAny -> AgdaAny -> ()
d__'8804'__352 = erased
-- Algebra.Lattice.Properties.Lattice.∨-∧-isOrderTheoreticLattice
d_'8744''45''8743''45'isOrderTheoreticLattice_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_348
d_'8744''45''8743''45'isOrderTheoreticLattice_356 ~v0 ~v1 v2
  = du_'8744''45''8743''45'isOrderTheoreticLattice_356 v2
du_'8744''45''8743''45'isOrderTheoreticLattice_356 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Structures.T_IsLattice_348
du_'8744''45''8743''45'isOrderTheoreticLattice_356 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Structures.C_constructor_424
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
         (coe
            MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_poset_162
            (coe du_'8743''45'semilattice_306 (coe v0))))
      (coe du_supremum_400 (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.NaturalOrder.Left.du_infimum_3754
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 (coe v0))
         (coe du_'8743''45'isSemilattice_304 (coe v0)))
-- Algebra.Lattice.Properties.Lattice._._._≤_
d__'8804'__368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  AgdaAny -> AgdaAny -> ()
d__'8804'__368 = erased
-- Algebra.Lattice.Properties.Lattice._.sound
d_sound_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sound_380 ~v0 ~v1 v2 v3 v4 v5 = du_sound_380 v2 v3 v4 v5
du_sound_380 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sound_380 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v2)
      v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v4 v5 v6 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v2)
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v2)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v2 v1))
            v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v2 v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v1 v2))
               v1
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v1 v2))
                  v1 v1
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))))
                     (coe v1))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'absorbs'45''8744'_3122
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)) v1
                     v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0))
                  (coe v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v2 v1)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v1 v2)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'comm_3094
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)) v2
                     v1)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8743''45'cong'737'_3124
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0))
               (coe v1) (coe v2)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v2 v1)
               (coe v3))))
-- Algebra.Lattice.Properties.Lattice._.complete
d_complete_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_complete_392 ~v0 ~v1 v2 v3 v4 v5 = du_complete_392 v2 v3 v4 v5
du_complete_392 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_complete_392 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))
      (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v2 v1)
      v2
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v4 v5 v6 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v2 v1)
         v2
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))))
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v2 v1)
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v2
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v2))
            v2
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v2))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v2
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v2 v1))
               v2
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v2
                     (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v2 v1))
                  v2 v2
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3092
                              (coe
                                 MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)))))
                     (coe v2))
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'absorbs'45''8743'_3120
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)) v2
                     v1))
               (coe
                  MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3132
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0))
                  (coe v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v2)
                  (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v2 v1)
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'comm_3100
                     (MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0)) v1
                     v2)))
            (coe
               MAlonzo.Code.Algebra.Lattice.Structures.du_'8744''45'cong'737'_3132
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d_isLattice_536 (coe v0))
               (coe v2) (coe v1)
               (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 v0 v1 v2)
               (coe v3))))
-- Algebra.Lattice.Properties.Lattice._.supremum
d_supremum_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_supremum_400 ~v0 ~v1 v2 v3 v4 = du_supremum_400 v2 v3 v4
du_supremum_400 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_supremum_400 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_sound_380 (coe v0) (coe v1)
         (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v1 v2)
         (coe
            MAlonzo.Code.Relation.Binary.Lattice.Structures.du_x'8804'x'8744'y_38
            (coe
               MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
               (coe du_'8744''45'semilattice_330 (coe v0)))
            (coe v1) (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            du_sound_380 (coe v0) (coe v2)
            (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v1 v2)
            (coe
               MAlonzo.Code.Relation.Binary.Lattice.Structures.du_y'8804'x'8744'y_50
               (coe
                  MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
                  (coe du_'8744''45'semilattice_330 (coe v0)))
               (coe v1) (coe v2)))
         (coe
            (\ v3 v4 v5 ->
               coe
                 du_sound_380 (coe v0)
                 (coe MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 v0 v1 v2)
                 (coe v3)
                 (coe
                    MAlonzo.Code.Relation.Binary.Lattice.Structures.du_'8744''45'least_64
                    (coe
                       MAlonzo.Code.Algebra.Lattice.Properties.Semilattice.du_'8743''45'isOrderTheoreticJoinSemilattice_178
                       (coe du_'8744''45'semilattice_330 (coe v0)))
                    v1 v2 v3 (coe du_complete_392 (coe v0) (coe v1) (coe v3) (coe v4))
                    (coe du_complete_392 (coe v0) (coe v2) (coe v3) (coe v5))))))
-- Algebra.Lattice.Properties.Lattice.∨-∧-orderTheoreticLattice
d_'8744''45''8743''45'orderTheoreticLattice_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_Lattice_394
d_'8744''45''8743''45'orderTheoreticLattice_412 ~v0 ~v1 v2
  = du_'8744''45''8743''45'orderTheoreticLattice_412 v2
du_'8744''45''8743''45'orderTheoreticLattice_412 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_512 ->
  MAlonzo.Code.Relation.Binary.Lattice.Bundles.T_Lattice_394
du_'8744''45''8743''45'orderTheoreticLattice_412 v0
  = coe
      MAlonzo.Code.Relation.Binary.Lattice.Bundles.C_constructor_498
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__532 (coe v0))
      (MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__534 (coe v0))
      (coe du_'8744''45''8743''45'isOrderTheoreticLattice_356 (coe v0))
