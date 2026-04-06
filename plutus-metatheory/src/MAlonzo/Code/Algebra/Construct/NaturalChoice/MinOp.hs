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

module MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Base
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Double
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Construct.NaturalChoice.MinOp._._≈_
d__'8776'__22 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__22 = erased
-- Algebra.Construct.NaturalChoice.MinOp._._≲_
d__'8818'__26 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> ()
d__'8818'__26 = erased
-- Algebra.Construct.NaturalChoice.MinOp._.Associative
d_Associative_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Associative_126 = erased
-- Algebra.Construct.NaturalChoice.MinOp._.Commutative
d_Commutative_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Commutative_130 = erased
-- Algebra.Construct.NaturalChoice.MinOp._.Congruent₁
d_Congruent'8321'_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  (AgdaAny -> AgdaAny) -> ()
d_Congruent'8321'_132 = erased
-- Algebra.Construct.NaturalChoice.MinOp._.Congruent₂
d_Congruent'8322'_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Congruent'8322'_134 = erased
-- Algebra.Construct.NaturalChoice.MinOp._.Idempotent
d_Idempotent_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Idempotent_140 = erased
-- Algebra.Construct.NaturalChoice.MinOp._.Identity
d_Identity_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Identity_146 = erased
-- Algebra.Construct.NaturalChoice.MinOp._.LeftIdentity
d_LeftIdentity_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftIdentity_172 = erased
-- Algebra.Construct.NaturalChoice.MinOp._.LeftZero
d_LeftZero_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftZero_180 = erased
-- Algebra.Construct.NaturalChoice.MinOp._.RightIdentity
d_RightIdentity_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightIdentity_202 = erased
-- Algebra.Construct.NaturalChoice.MinOp._.RightZero
d_RightZero_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightZero_210 = erased
-- Algebra.Construct.NaturalChoice.MinOp._.Selective
d_Selective_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Selective_212 = erased
-- Algebra.Construct.NaturalChoice.MinOp._.Zero
d_Zero_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Zero_230 = erased
-- Algebra.Construct.NaturalChoice.MinOp._.IsBand
d_IsBand_242 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Construct.NaturalChoice.MinOp._.IsCommutativeSemigroup
d_IsCommutativeSemigroup_266 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Construct.NaturalChoice.MinOp._.IsMagma
d_IsMagma_322 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Construct.NaturalChoice.MinOp._.IsMonoid
d_IsMonoid_334 a0 a1 a2 a3 a4 a5 a6 = ()
-- Algebra.Construct.NaturalChoice.MinOp._.IsSelectiveMagma
d_IsSelectiveMagma_374 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Construct.NaturalChoice.MinOp._.IsSemigroup
d_IsSemigroup_378 a0 a1 a2 a3 a4 a5 = ()
-- Algebra.Construct.NaturalChoice.MinOp._.IsBand.idem
d_idem_506 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 -> AgdaAny -> AgdaAny
d_idem_506 v0
  = coe MAlonzo.Code.Algebra.Structures.d_idem_536 (coe v0)
-- Algebra.Construct.NaturalChoice.MinOp._.IsBand.isSemigroup
d_isSemigroup_514 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_526 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_514 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_534 (coe v0)
-- Algebra.Construct.NaturalChoice.MinOp._.IsCommutativeSemigroup.comm
d_comm_870 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_870 v0
  = coe MAlonzo.Code.Algebra.Structures.d_comm_578 (coe v0)
-- Algebra.Construct.NaturalChoice.MinOp._.IsCommutativeSemigroup.isSemigroup
d_isSemigroup_880 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_880 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_576 (coe v0)
-- Algebra.Construct.NaturalChoice.MinOp._.IsMagma.isEquivalence
d_isEquivalence_1674 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_1674 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_186 (coe v0)
-- Algebra.Construct.NaturalChoice.MinOp._.IsMagma.∙-cong
d_'8729''45'cong_1688 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_1688 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188 (coe v0)
-- Algebra.Construct.NaturalChoice.MinOp._.IsMonoid.identity
d_identity_1784 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1784 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_724 (coe v0)
-- Algebra.Construct.NaturalChoice.MinOp._.IsMonoid.isSemigroup
d_isSemigroup_1796 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_1796 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_722 (coe v0)
-- Algebra.Construct.NaturalChoice.MinOp._.IsSelectiveMagma.isMagma
d_isMagma_2506 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2506 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v0)
-- Algebra.Construct.NaturalChoice.MinOp._.IsSelectiveMagma.sel
d_sel_2514 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_2514 v0
  = coe MAlonzo.Code.Algebra.Structures.d_sel_460 (coe v0)
-- Algebra.Construct.NaturalChoice.MinOp._.IsSemigroup.assoc
d_assoc_2530 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_2530 v0
  = coe MAlonzo.Code.Algebra.Structures.d_assoc_498 (coe v0)
-- Algebra.Construct.NaturalChoice.MinOp._.IsSemigroup.isMagma
d_isMagma_2534 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_2534 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_496 (coe v0)
-- Algebra.Construct.NaturalChoice.MinOp.x⊓y≤x
d_x'8851'y'8804'x_2924 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'x_2924 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_x'8851'y'8804'x_2924 v3 v4 v5 v6
du_x'8851'y'8804'x_2924 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'x_2924 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_142
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                 (coe v0))
              v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
           -> coe
                MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
                (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                   (coe
                      MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                      (coe v0)))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v2 v3)
                v2
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                   v1 v2 v3 v5)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
           -> coe
                MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                   (coe
                      MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                      (coe v0)))
                (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v2 v3)
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                   (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v2 v3)
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                      v1 v2 v3 v5))
                (coe v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinOp.x⊓y≤y
d_x'8851'y'8804'y_2950 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8804'y_2950 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_x'8851'y'8804'y_2950 v3 v4 v5 v6
du_x'8851'y'8804'y_2950 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8804'y_2950 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_142
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                 (coe v0))
              v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
           -> coe
                MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                   (coe
                      MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                      (coe v0)))
                (coe v3) (coe v2)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v2 v3)
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                   (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v2 v3)
                   v2
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                      v1 v2 v3 v5))
                (coe v5)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
           -> coe
                MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
                (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                   (coe
                      MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                      (coe v0)))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v2 v3)
                v3
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                   v1 v2 v3 v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinOp.⊓-comm
d_'8851''45'comm_2972 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'comm_2972 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'8851''45'comm_2972 v3 v4 v5 v6
du_'8851''45'comm_2972 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'comm_2972 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_142
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                 (coe v0))
              v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
           -> coe
                MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                   (coe
                      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                      (coe
                         MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                         (coe v0))))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v2 v3)
                v2
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v3 v2)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                   v1 v2 v3 v5)
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                   (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3 v2)
                   v2
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                      v1 v3 v2 v5))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
           -> coe
                MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                   (coe
                      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                      (coe
                         MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                         (coe v0))))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v2 v3)
                v3
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v3 v2)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                   v1 v2 v3 v5)
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                   (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3 v2)
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                      v1 v3 v2 v5))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinOp.⊓-congˡ
d_'8851''45'cong'737'_2998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'737'_2998 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_'8851''45'cong'737'_2998 v3 v4 v5 v6 v7 v8
du_'8851''45'cong'737'_2998 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'737'_2998 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_142
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                 (coe v0))
              v2 v3 in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v2 v3)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v2 v4)
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v2 v3)
                   v2
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v2 v4)
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0)))))
                      v2
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v2 v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v2 v4)
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v2 v4))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                         v1 v2 v4
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0)))
                            (coe v2) (coe v3) (coe v4) (coe v5) (coe v7))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                      v1 v2 v3 v7))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v2 v3)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v2 v4)
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v2 v3)
                   v3
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v2 v4)
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      v3 v4
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v2 v4)
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                               (coe
                                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                     (coe v0)))))
                         v4
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v2 v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v2 v4)
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                               (coe
                                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                     (coe v0))))
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                               v2 v4))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                            v1 v2 v4
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
                               (coe
                                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                     (coe v0)))
                               (coe v2) (coe v3) (coe v4) (coe v5) (coe v7))))
                      v5)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                      v1 v2 v3 v7))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinOp.⊓-congʳ
d_'8851''45'cong'691'_3036 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong'691'_3036 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_'8851''45'cong'691'_3036 v3 v4 v5 v6 v7 v8
du_'8851''45'cong'691'_3036 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong'691'_3036 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
         v3 v2)
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
         v4 v2)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                  (coe v0))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
            v3 v2)
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
            v2 v3)
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
            v4 v2)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                     (coe v0))))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
               v2 v3)
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
               v2 v4)
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
               v4 v2)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                        (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v2 v4)
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v4 v2)
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v4 v2)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                     v4 v2))
               (coe du_'8851''45'comm_2972 (coe v0) (coe v1) (coe v2) (coe v4)))
            (coe
               du_'8851''45'cong'737'_2998 (coe v0) (coe v1) (coe v2) (coe v3)
               (coe v4) (coe v5)))
         (coe du_'8851''45'comm_2972 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-cong
d_'8851''45'cong_3046 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'cong_3046 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_'8851''45'cong_3046 v3 v4 v5 v6 v7 v8 v9 v10
du_'8851''45'cong_3046 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'cong_3046 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
               (coe v0))))
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
            v2)
         (\ v8 v9 -> v8) v4 v5)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v8 v9 -> v9)
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
            v2)
         v4 v5)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v8 v9 -> v9)
         (\ v8 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
              v8 v5)
         v2 v3)
      (coe
         du_'8851''45'cong'737'_2998 (coe v0) (coe v1) (coe v2) (coe v4)
         (coe v5) (coe v7))
      (coe
         du_'8851''45'cong'691'_3036 (coe v0) (coe v1) (coe v5) (coe v2)
         (coe v3) (coe v6))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-assoc
d_'8851''45'assoc_3060 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'assoc_3060 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_'8851''45'assoc_3060 v3 v4 v5 v6 v7
du_'8851''45'assoc_3060 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'assoc_3060 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_142
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                 (coe v0))
              v2 v3 in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Relation.Binary.Structures.d_total_142
                 (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                    (coe v0))
                 v3 v4 in
       coe
         (case coe v5 of
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
              -> case coe v6 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                     -> coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                          (coe
                             MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                             (coe
                                MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                                v2 v3)
                             v4)
                          (coe
                             MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                             v2
                             (coe
                                MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                                v3 v4))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                      (coe v0))))
                             (coe
                                MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                                (coe
                                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                   v1 v2 v3)
                                v4)
                             (coe
                                MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                                v2 v4)
                             (coe
                                MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                                v2
                                (coe
                                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                   v1 v3 v4))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                         (coe v0))))
                                (coe
                                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                   v1 v2 v4)
                                v2
                                (coe
                                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                   v1 v2
                                   (coe
                                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                      v1 v3 v4))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                            (coe v0))))
                                   (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                               (coe v0)))))
                                   v2
                                   (coe
                                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                      v1 v2 v3)
                                   (coe
                                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                      v1 v2
                                      (coe
                                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                         v1 v3 v4))
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                               (coe v0))))
                                      (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                                  (coe v0)))))
                                      (coe
                                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                         v1 v2 v3)
                                      (coe
                                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                         v1 v2
                                         (coe
                                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                            v1 v3 v4))
                                      (coe
                                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                         v1 v2
                                         (coe
                                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                            v1 v3 v4))
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                                  (coe v0))))
                                         (coe
                                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                            v1 v2
                                            (coe
                                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                               v1 v3 v4)))
                                      (coe
                                         du_'8851''45'cong'737'_2998 (coe v0) (coe v1) (coe v2)
                                         (coe
                                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                            v1 v3 v4)
                                         (coe v3)
                                         (coe
                                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                                            v1 v3 v4 v8)))
                                   (coe
                                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                                      v1 v2 v3 v7))
                                (coe
                                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                                   v1 v2 v4
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
                                      (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                            (coe v0)))
                                      v2 v3 v4 v7 v8)))
                             (coe
                                du_'8851''45'cong'691'_3036 (coe v0) (coe v1) (coe v4)
                                (coe
                                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                   v1 v2 v3)
                                (coe v2)
                                (coe
                                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                                   v1 v2 v3 v7)))
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
                     -> coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                          (coe
                             MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                             (coe
                                MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                                v2 v3)
                             v4)
                          (coe
                             MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                             v2
                             (coe
                                MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                                v3 v4))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                      (coe v0))))
                             (coe
                                MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                                (coe
                                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                   v1 v2 v3)
                                v4)
                             (coe
                                MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                                v2 v4)
                             (coe
                                MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                                v2
                                (coe
                                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                   v1 v3 v4))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                         (coe v0))))
                                (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                            (coe v0)))))
                                (coe
                                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                   v1 v2 v4)
                                (coe
                                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                   v1 v2
                                   (coe
                                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                      v1 v3 v4))
                                (coe
                                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                   v1 v2
                                   (coe
                                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                      v1 v3 v4))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                            (coe v0))))
                                   (coe
                                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                      v1 v2
                                      (coe
                                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                         v1 v3 v4)))
                                (coe
                                   du_'8851''45'cong'737'_2998 (coe v0) (coe v1) (coe v2)
                                   (coe
                                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                      v1 v3 v4)
                                   (coe v4)
                                   (coe
                                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                                      v1 v3 v4 v8)))
                             (coe
                                du_'8851''45'cong'691'_3036 (coe v0) (coe v1) (coe v4)
                                (coe
                                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                   v1 v2 v3)
                                (coe v2)
                                (coe
                                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                                   v1 v2 v3 v7)))
                   _ -> MAlonzo.RTE.mazUnreachableError
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
              -> coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v2 v3)
                      v4)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v2
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v3 v4))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v2 v3)
                         v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v3 v4)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v2
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v3 v4))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                               (coe
                                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                     (coe v0)))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v3 v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v2
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                               v3 v4))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v2
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                               v3 v4))
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                               (coe
                                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                     (coe v0))))
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                               v2
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                  v1 v3 v4)))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                            v1 v2
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                               v3 v4)
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_trans_90
                               (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                     (coe v0)))
                               (coe
                                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
                                  v1 v3 v4)
                               v3 v2
                               (coe du_x'8851'y'8804'x_2924 (coe v0) (coe v1) (coe v3) (coe v4))
                               v7)))
                      (coe
                         du_'8851''45'cong'691'_3036 (coe v0) (coe v1) (coe v4)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            v2 v3)
                         (coe v3)
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                            v1 v2 v3 v7)))
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-idem
d_'8851''45'idem_3100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny
d_'8851''45'idem_3100 ~v0 ~v1 ~v2 v3 v4 v5
  = du_'8851''45'idem_3100 v3 v4 v5
du_'8851''45'idem_3100 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny
du_'8851''45'idem_3100 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
      v1 v2 v2
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_104
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
               (coe v0)))
         (coe v2))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-sel
d_'8851''45'sel_3104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_3104 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'8851''45'sel_3104 v3 v4 v5 v6
du_'8851''45'sel_3104 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8851''45'sel_3104 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Sum.Base.du_map_84
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
         v1 v2 v3)
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
         v1 v2 v3)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_total_142
         (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
            (coe v0))
         v2 v3)
-- Algebra.Construct.NaturalChoice.MinOp.⊓-identityˡ
d_'8851''45'identity'737'_3112 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'737'_3112 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
      v0 v1 v3 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinOp.⊓-identityʳ
d_'8851''45'identity'691'_3118 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'identity'691'_3118 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
      v0 v3 v1 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinOp.⊓-identity
d_'8851''45'identity_3124 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'identity_3124 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
              v0 v1 v3 (coe v2 v3)))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
              v0 v3 v1 (coe v2 v3)))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-zeroˡ
d_'8851''45'zero'737'_3130 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'737'_3130 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
      v0 v1 v3 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinOp.⊓-zeroʳ
d_'8851''45'zero'691'_3136 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_'8851''45'zero'691'_3136 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
      v0 v3 v1 (coe v2 v3)
-- Algebra.Construct.NaturalChoice.MinOp.⊓-zero
d_'8851''45'zero_3142 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'zero_3142 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
              v0 v1 v3 (coe v2 v3)))
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
              v0 v3 v1 (coe v2 v3)))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-isMagma
d_'8851''45'isMagma_3146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_'8851''45'isMagma_3146 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isMagma_3146 v3 v4
du_'8851''45'isMagma_3146 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_'8851''45'isMagma_3146 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
               (coe v0))))
      (coe du_'8851''45'cong_3046 (coe v0) (coe v1))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-isSemigroup
d_'8851''45'isSemigroup_3148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_'8851''45'isSemigroup_3148 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isSemigroup_3148 v3 v4
du_'8851''45'isSemigroup_3148 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_'8851''45'isSemigroup_3148 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe du_'8851''45'isMagma_3146 (coe v0) (coe v1))
      (coe du_'8851''45'assoc_3060 (coe v0) (coe v1))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-isBand
d_'8851''45'isBand_3150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_'8851''45'isBand_3150 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isBand_3150 v3 v4
du_'8851''45'isBand_3150 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_'8851''45'isBand_3150 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_564
      (coe du_'8851''45'isSemigroup_3148 (coe v0) (coe v1))
      (coe du_'8851''45'idem_3100 (coe v0) (coe v1))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_3152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
d_'8851''45'isCommutativeSemigroup_3152 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isCommutativeSemigroup_3152 v3 v4
du_'8851''45'isCommutativeSemigroup_3152 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_568
du_'8851''45'isCommutativeSemigroup_3152 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_608
      (coe du_'8851''45'isSemigroup_3148 (coe v0) (coe v1))
      (coe du_'8851''45'comm_2972 (coe v0) (coe v1))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_3154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450
d_'8851''45'isSelectiveMagma_3154 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'isSelectiveMagma_3154 v3 v4
du_'8851''45'isSelectiveMagma_3154 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450
du_'8851''45'isSelectiveMagma_3154 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_484
      (coe du_'8851''45'isMagma_3146 (coe v0) (coe v1))
      (coe du_'8851''45'sel_3104 (coe v0) (coe v1))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-isMonoid
d_'8851''45'isMonoid_3158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
d_'8851''45'isMonoid_3158 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'8851''45'isMonoid_3158 v3 v4 v5 v6
du_'8851''45'isMonoid_3158 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_712
du_'8851''45'isMonoid_3158 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_758
      (coe du_'8851''45'isSemigroup_3148 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            (\ v4 ->
               coe
                 MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                 v1 v2 v4 (coe v3 v4)))
         (coe
            (\ v4 ->
               coe
                 MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                 v1 v4 v2 (coe v3 v4))))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-rawMagma
d_'8851''45'rawMagma_3162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'8851''45'rawMagma_3162 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8851''45'rawMagma_3162 v4
du_'8851''45'rawMagma_3162 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_'8851''45'rawMagma_3162 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_68
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
         (coe v0))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-magma
d_'8851''45'magma_3164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_74
d_'8851''45'magma_3164 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'magma_3164 v3 v4
du_'8851''45'magma_3164 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_74
du_'8851''45'magma_3164 v0 v1
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_124
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
         (coe v1))
      (coe du_'8851''45'isMagma_3146 (coe v0) (coe v1))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-semigroup
d_'8851''45'semigroup_3166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
d_'8851''45'semigroup_3166 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'semigroup_3166 v3 v4
du_'8851''45'semigroup_3166 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558
du_'8851''45'semigroup_3166 v0 v1
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_614
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
         (coe v1))
      (coe du_'8851''45'isSemigroup_3148 (coe v0) (coe v1))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-band
d_'8851''45'band_3168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_620
d_'8851''45'band_3168 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'band_3168 v3 v4
du_'8851''45'band_3168 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_Band_620
du_'8851''45'band_3168 v0 v1
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_682
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
         (coe v1))
      (coe du_'8851''45'isBand_3150 (coe v0) (coe v1))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_3170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
d_'8851''45'commutativeSemigroup_3170 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'commutativeSemigroup_3170 v3 v4
du_'8851''45'commutativeSemigroup_3170 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_688
du_'8851''45'commutativeSemigroup_3170 v0 v1
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_754
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
         (coe v1))
      (coe du_'8851''45'isCommutativeSemigroup_3152 (coe v0) (coe v1))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-selectiveMagma
d_'8851''45'selectiveMagma_3172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_130
d_'8851''45'selectiveMagma_3172 ~v0 ~v1 ~v2 v3 v4
  = du_'8851''45'selectiveMagma_3172 v3 v4
du_'8851''45'selectiveMagma_3172 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_130
du_'8851''45'selectiveMagma_3172 v0 v1
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_184
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
         (coe v1))
      (coe du_'8851''45'isSelectiveMagma_3154 (coe v0) (coe v1))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-monoid
d_'8851''45'monoid_3176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_914
d_'8851''45'monoid_3176 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_'8851''45'monoid_3176 v3 v4 v5 v6
du_'8851''45'monoid_3176 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> MAlonzo.Code.Algebra.Bundles.T_Monoid_914
du_'8851''45'monoid_3176 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Bundles.C_constructor_990
      (MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122
         (coe v1))
      v2
      (coe
         du_'8851''45'isMonoid_3158 (coe v0) (coe v1) (coe v2) (coe v3))
-- Algebra.Construct.NaturalChoice.MinOp.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_3184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'x'8658'x'8804'y_3184 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_x'8851'y'8776'x'8658'x'8804'y_3184 v3 v4 v5 v6 v7
du_x'8851'y'8776'x'8658'x'8804'y_3184 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'x'8658'x'8804'y_3184 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_142
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                 (coe v0))
              v2 v3 in
    coe
      (case coe v5 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6 -> coe v6
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
           -> coe
                MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88
                (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                   (coe
                      MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                      (coe v0)))
                v2 v3
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                   (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   v2
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v2 v3)
                   v3
                   (coe
                      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v2 v3)
                      v2 v4)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                      v1 v2 v3 v6))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinOp.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_3216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8851'y'8776'y'8658'y'8804'x_3216 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_x'8851'y'8776'y'8658'y'8804'x_3216 v3 v4 v5 v6 v7
du_x'8851'y'8776'y'8658'y'8804'x_3216 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8851'y'8776'y'8658'y'8804'x_3216 v0 v1 v2 v3 v4
  = coe
      du_x'8851'y'8776'x'8658'x'8804'y_3184 (coe v0) (coe v1) (coe v3)
      (coe v2)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
            v3 v2)
         (coe v3)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                     (coe v0))))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
               v3 v2)
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
               v2 v3)
            v3
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                        (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v2 v3)
               v3 v3
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                           (coe v0))))
                  (coe v3))
               v4)
            (coe du_'8851''45'comm_2972 (coe v0) (coe v1) (coe v3) (coe v2))))
-- Algebra.Construct.NaturalChoice.MinOp.mono-≤-distrib-⊓
d_mono'45''8804''45'distrib'45''8851'_3230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_mono'45''8804''45'distrib'45''8851'_3230 ~v0 ~v1 ~v2 v3 v4 v5 v6
                                           v7 v8 v9
  = du_mono'45''8804''45'distrib'45''8851'_3230 v3 v4 v5 v6 v7 v8 v9
du_mono'45''8804''45'distrib'45''8851'_3230 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_mono'45''8804''45'distrib'45''8851'_3230 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d_total_142
              (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                 (coe v0))
              v5 v6 in
    coe
      (case coe v7 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   v2
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v5 v6))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   (coe v2 v5) (coe v2 v6))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      v2
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v5 v6))
                   (coe v2 v5)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      (coe v2 v5) (coe v2 v6))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0)))))
                      (coe v2 v5)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         (coe v2 v5) (coe v2 v6))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         (coe v2 v5) (coe v2 v6))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            (coe v2 v5) (coe v2 v6)))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                         v1 (coe v2 v5) (coe v2 v6) (coe v4 v5 v6 v8)))
                   (coe
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v5 v6)
                      v5
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                         v1 v5 v6 v8)))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
           -> coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
                (coe
                   v2
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v5 v6))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   (coe v2 v5) (coe v2 v6))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      v2
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v5 v6))
                   (coe v2 v6)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      (coe v2 v5) (coe v2 v6))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                            (coe
                               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                               (coe v0))))
                      (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0)))))
                      (coe v2 v6)
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         (coe v2 v5) (coe v2 v6))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         (coe v2 v5) (coe v2 v6))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                            (coe
                               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                               (coe
                                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                                  (coe v0))))
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                            (coe v2 v5) (coe v2 v6)))
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                         v1 (coe v2 v5) (coe v2 v6) (coe v4 v6 v5 v8)))
                   (coe
                      v3
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                         v5 v6)
                      v6
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                         v1 v5 v6 v8)))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinOp.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_3276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'x'8851'z'8804'y_3276 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_x'8804'y'8658'x'8851'z'8804'y_3276 v3 v4 v5 v6 v7 v8
du_x'8804'y'8658'x'8851'z'8804'y_3276 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'x'8851'z'8804'y_3276 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
         v2 v4)
      v2 v3
      (coe du_x'8851'y'8804'x_2924 (coe v0) (coe v1) (coe v2) (coe v4))
      v5
-- Algebra.Construct.NaturalChoice.MinOp.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_3288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8658'z'8851'x'8804'y_3288 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_x'8804'y'8658'z'8851'x'8804'y_3288 v3 v4 v5 v6 v7 v8
du_x'8804'y'8658'z'8851'x'8804'y_3288 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8658'z'8851'x'8804'y_3288 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
         v4 v2)
      v2 v3
      (coe du_x'8851'y'8804'y_2950 (coe v0) (coe v1) (coe v4) (coe v2))
      v5
-- Algebra.Construct.NaturalChoice.MinOp.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_3300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'y_3300 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_x'8804'y'8851'z'8658'x'8804'y_3300 v3 v4 v5 v6 v7 v8
du_x'8804'y'8851'z'8658'x'8804'y_3300 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'y_3300 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
            (coe v0)))
      v2
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
         v3 v4)
      v3 v5
      (coe du_x'8851'y'8804'x_2924 (coe v0) (coe v1) (coe v3) (coe v4))
-- Algebra.Construct.NaturalChoice.MinOp.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_3314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8804'y'8851'z'8658'x'8804'z_3314 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_x'8804'y'8851'z'8658'x'8804'z_3314 v3 v4 v5 v6 v7 v8
du_x'8804'y'8851'z'8658'x'8804'z_3314 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8804'y'8851'z'8658'x'8804'z_3314 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_90
      (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
            (coe v0)))
      v2
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
         v3 v4)
      v4 v5
      (coe du_x'8851'y'8804'y_2950 (coe v0) (coe v1) (coe v3) (coe v4))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-mono-≤
d_'8851''45'mono'45''8804'_3322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'45''8804'_3322 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9
                                v10
  = du_'8851''45'mono'45''8804'_3322 v3 v4 v5 v6 v7 v8 v9 v10
du_'8851''45'mono'45''8804'_3322 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'45''8804'_3322 v0 v1 v2 v3 v4 v5 v6 v7
  = let v8
          = coe
              MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
              (coe
                 (\ v8 ->
                    coe
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8804'y'8658'x'8851'y'8776'x_128
                         v1 v3 v5 v8)))
              (coe
                 (\ v8 ->
                    coe
                      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                      (coe
                         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d_x'8805'y'8658'x'8851'y'8776'y_134
                         v1 v3 v5 v8)))
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_total_142
                 (MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                    (coe v0))
                 v3 v5) in
    coe
      (case coe v8 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
           -> coe
                MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                   (coe
                      MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                      (coe v0)))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v2 v4)
                (coe v3)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v3 v5)
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                   (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3 v5)
                   v3 v9)
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_trans_90
                   (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                      (coe
                         MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                         (coe v0)))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v2 v4)
                   v2 v3
                   (coe du_x'8851'y'8804'x_2924 (coe v0) (coe v1) (coe v2) (coe v4))
                   v6)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
           -> coe
                MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'691''45''8776'_112
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                   (coe
                      MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                      (coe v0)))
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v2 v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                   v3 v5)
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                   (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                         (coe
                            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                            (coe v0))))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v3 v5)
                   v5 v9)
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_trans_90
                   (MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                      (coe
                         MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                         (coe v0)))
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                      v2 v4)
                   v4 v5
                   (coe du_x'8851'y'8804'y_2950 (coe v0) (coe v1) (coe v2) (coe v4))
                   v7)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.NaturalChoice.MinOp.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_3372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'737''45''8804'_3372 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_'8851''45'mono'737''45''8804'_3372 v3 v4 v5 v6 v7 v8
du_'8851''45'mono'737''45''8804'_3372 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'737''45''8804'_3372 v0 v1 v2 v3 v4 v5
  = coe
      du_'8851''45'mono'45''8804'_3322 (coe v0) (coe v1) (coe v3)
      (coe v4) (coe v2) (coe v2) (coe v5)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_104
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
               (coe v0)))
         (coe v2))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_3382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'mono'691''45''8804'_3382 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_'8851''45'mono'691''45''8804'_3382 v3 v4 v5 v6 v7 v8
du_'8851''45'mono'691''45''8804'_3382 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'mono'691''45''8804'_3382 v0 v1 v2 v3 v4 v5
  = coe
      du_'8851''45'mono'45''8804'_3322 (coe v0) (coe v1) (coe v2)
      (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.du_refl_104
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
               (coe v0)))
         (coe v2))
      (coe v5)
-- Algebra.Construct.NaturalChoice.MinOp.⊓-glb
d_'8851''45'glb_3394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'glb_3394 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9
  = du_'8851''45'glb_3394 v3 v4 v5 v6 v7 v8 v9
du_'8851''45'glb_3394 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'glb_3394 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_'8818''45'resp'737''45''8776'_106
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
            (coe v0)))
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
         v3 v4)
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
         v2 v2)
      (coe v2) (coe du_'8851''45'idem_3100 (coe v0) (coe v1) (coe v2))
      (coe
         du_'8851''45'mono'45''8804'_3322 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v2) (coe v4) (coe v5) (coe v6))
-- Algebra.Construct.NaturalChoice.MinOp.⊓-triangulate
d_'8851''45'triangulate_3408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8851''45'triangulate_3408 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7
  = du_'8851''45'triangulate_3408 v3 v4 v5 v6 v7
du_'8851''45'triangulate_3408 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8851''45'triangulate_3408 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__128
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_equalitySubRelation_152)
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
            v2 v3)
         v4)
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
            v2 v3)
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
            v3 v4))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                  (coe v0))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                     (coe v0)))))
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
               v2 v3)
            v4)
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
               v2
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v3 v3))
            v4)
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
               v2 v3)
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
               v3 v4))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                     (coe v0))))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                     v3 v3))
               v4)
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
               v2
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  (coe
                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                     v3 v3)
                  v4))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v2 v3)
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v3 v4))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                        (coe v0))))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                     (coe
                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                        v3 v3)
                     v4))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v2
                  (coe
                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                     v3
                     (coe
                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                        v3 v4)))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  (coe
                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                     v2 v3)
                  (coe
                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                     v3 v4))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_'8776''45'go_106
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                           (coe v0))))
                  (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                              (coe v0)))))
                  (coe
                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                     v2
                     (coe
                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                        v3
                        (coe
                           MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                           v3 v4)))
                  (coe
                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                     (coe
                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                        v2 v3)
                     (coe
                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                        v3 v4))
                  (coe
                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                     (coe
                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                        v2 v3)
                     (coe
                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                        v3 v4))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Double.du_stop_116
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
                              (coe v0))))
                     (coe
                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                        (coe
                           MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                           v2 v3)
                        (coe
                           MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                           v3 v4)))
                  (coe
                     du_'8851''45'assoc_3060 (coe v0) (coe v1) (coe v2) (coe v3)
                     (coe
                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                        v3 v4)))
               (coe
                  du_'8851''45'cong'737'_2998 (coe v0) (coe v1) (coe v2)
                  (coe
                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                     (coe
                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                        v3 v3)
                     v4)
                  (coe
                     MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                     v3
                     (coe
                        MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                        v3 v4))
                  (coe
                     du_'8851''45'assoc_3060 (coe v0) (coe v1) (coe v3) (coe v3)
                     (coe v4))))
            (coe
               du_'8851''45'assoc_3060 (coe v0) (coe v1) (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v3 v3)
               (coe v4)))
         (coe
            du_'8851''45'cong'691'_3036 (coe v0) (coe v1) (coe v4)
            (coe
               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v2)
               (\ v5 v6 -> v5)
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v3 v3)
               v3)
            (coe
               MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
               (\ v5 v6 -> v6)
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v2)
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v3 v3)
               v3)
            (coe
               du_'8851''45'cong'737'_2998 (coe v0) (coe v1) (coe v2)
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.d__'8851'__122 v1
                  v3 v3)
               (coe v3) (coe du_'8851''45'idem_3100 (coe v0) (coe v1) (coe v3)))))
