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

module MAlonzo.Code.Algebra.Properties.AbelianGroup where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Properties.Group qualified
import MAlonzo.Code.Algebra.Properties.Loop qualified
import MAlonzo.Code.Algebra.Properties.QQuasigroup qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Base.Single qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Syntax qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Properties.AbelianGroup._._//_
d__'47''47'__14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__14 ~v0 ~v1 v2 = du__'47''47'__14 v2
du__'47''47'__14 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__14 v0
  = let v1 = MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du__'47''47'__1098 (coe v1)
            (coe v2)))
-- Algebra.Properties.AbelianGroup._.//-cong₂
d_'47''47''45'cong'8322'_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'cong'8322'_158 ~v0 ~v1 v2
  = du_'47''47''45'cong'8322'_158 v2
du_'47''47''45'cong'8322'_158 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'cong'8322'_158 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'47''47''45'cong'8322'_522
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.//-rightDivides
d_'47''47''45'rightDivides_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'47''47''45'rightDivides_160 ~v0 ~v1 v2
  = du_'47''47''45'rightDivides_160 v2
du_'47''47''45'rightDivides_160 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'47''47''45'rightDivides_160 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'47''47''45'rightDivides_554
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.//-rightDividesʳ
d_'47''47''45'rightDivides'691'_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'rightDivides'691'_162 ~v0 ~v1 v2
  = du_'47''47''45'rightDivides'691'_162 v2
du_'47''47''45'rightDivides'691'_162 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'rightDivides'691'_162 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'47''47''45'rightDivides'691'_548
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.//-rightDividesˡ
d_'47''47''45'rightDivides'737'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'47''47''45'rightDivides'737'_164 ~v0 ~v1 v2
  = du_'47''47''45'rightDivides'737'_164 v2
du_'47''47''45'rightDivides'737'_164 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'47''47''45'rightDivides'737'_164 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'47''47''45'rightDivides'737'_542
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.\\-cong₂
d_'92''92''45'cong'8322'_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'cong'8322'_166 ~v0 ~v1 v2
  = du_'92''92''45'cong'8322'_166 v2
du_'92''92''45'cong'8322'_166 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'cong'8322'_166 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'92''92''45'cong'8322'_516
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.\\-leftDivides
d_'92''92''45'leftDivides_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'92''92''45'leftDivides_168 ~v0 ~v1 v2
  = du_'92''92''45'leftDivides_168 v2
du_'92''92''45'leftDivides_168 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'92''92''45'leftDivides_168 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'92''92''45'leftDivides_540
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.\\-leftDividesʳ
d_'92''92''45'leftDivides'691'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'leftDivides'691'_170 ~v0 ~v1 v2
  = du_'92''92''45'leftDivides'691'_170 v2
du_'92''92''45'leftDivides'691'_170 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'leftDivides'691'_170 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'92''92''45'leftDivides'691'_534
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.\\-leftDividesˡ
d_'92''92''45'leftDivides'737'_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''45'leftDivides'737'_172 ~v0 ~v1 v2
  = du_'92''92''45'leftDivides'737'_172 v2
du_'92''92''45'leftDivides'737'_172 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''45'leftDivides'737'_172 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'92''92''45'leftDivides'737'_528
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.\\≗flip-//⇒comm
d_'92''92''8791'flip'45''47''47''8658'comm_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'92''92''8791'flip'45''47''47''8658'comm_174 ~v0 ~v1 v2
  = du_'92''92''8791'flip'45''47''47''8658'comm_174 v2
du_'92''92''8791'flip'45''47''47''8658'comm_174 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'92''92''8791'flip'45''47''47''8658'comm_174 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'92''92''8791'flip'45''47''47''8658'comm_680
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.comm⇒\\≗flip-//
d_comm'8658''92''92''8791'flip'45''47''47'_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_comm'8658''92''92''8791'flip'45''47''47'_176 ~v0 ~v1 v2
  = du_comm'8658''92''92''8791'flip'45''47''47'_176 v2
du_comm'8658''92''92''8791'flip'45''47''47'_176 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_comm'8658''92''92''8791'flip'45''47''47'_176 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_comm'8658''92''92''8791'flip'45''47''47'_692
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.identity-unique
d_identity'45'unique_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_identity'45'unique_178 ~v0 ~v1 v2 = du_identity'45'unique_178 v2
du_identity'45'unique_178 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_identity'45'unique_178 v0
  = let v1
          = coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Loop.du_identity'45'unique_326
         (coe MAlonzo.Code.Algebra.Properties.Group.du_loop_574 (coe v1)))
-- Algebra.Properties.AbelianGroup._.identityʳ-unique
d_identity'691''45'unique_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_identity'691''45'unique_180 ~v0 ~v1 v2
  = du_identity'691''45'unique_180 v2
du_identity'691''45'unique_180 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_identity'691''45'unique_180 v0
  = let v1
          = coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Loop.du_identity'691''45'unique_316
         (coe MAlonzo.Code.Algebra.Properties.Group.du_loop_574 (coe v1)))
-- Algebra.Properties.AbelianGroup._.identityˡ-unique
d_identity'737''45'unique_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_identity'737''45'unique_182 ~v0 ~v1 v2
  = du_identity'737''45'unique_182 v2
du_identity'737''45'unique_182 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_identity'737''45'unique_182 v0
  = let v1
          = coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.Loop.du_identity'737''45'unique_304
         (coe MAlonzo.Code.Algebra.Properties.Group.du_loop_574 (coe v1)))
-- Algebra.Properties.AbelianGroup._.inverseʳ-unique
d_inverse'691''45'unique_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691''45'unique_184 ~v0 ~v1 v2
  = du_inverse'691''45'unique_184 v2
du_inverse'691''45'unique_184 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'691''45'unique_184 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_inverse'691''45'unique_600
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.inverseˡ-unique
d_inverse'737''45'unique_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737''45'unique_186 ~v0 ~v1 v2
  = du_inverse'737''45'unique_186 v2
du_inverse'737''45'unique_186 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'737''45'unique_186 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_inverse'737''45'unique_588
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.isLoop
d_isLoop_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026
d_isLoop_188 ~v0 ~v1 v2 = du_isLoop_188 v2
du_isLoop_188 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Structures.T_IsLoop_3026
du_isLoop_188 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_isLoop_572
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.isQuasigroup
d_isQuasigroup_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
d_isQuasigroup_190 ~v0 ~v1 v2 = du_isQuasigroup_190 v2
du_isQuasigroup_190 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Structures.T_IsQuasigroup_2944
du_isQuasigroup_190 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_isQuasigroup_556
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.loop
d_loop_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_Loop_4346
d_loop_192 ~v0 ~v1 v2 = du_loop_192 v2
du_loop_192 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_Loop_4346
du_loop_192 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_loop_574
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.quasigroup
d_quasigroup_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246
d_quasigroup_194 ~v0 ~v1 v2 = du_quasigroup_194 v2
du_quasigroup_194 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246
du_quasigroup_194 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_558
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.x∙y⁻¹≈ε⇒x≈y
d_x'8729'y'8315''185''8776'ε'8658'x'8776'y_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'y'8315''185''8776'ε'8658'x'8776'y_196 ~v0 ~v1 v2
  = du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_196 v2
du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_196 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_196 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_x'8729'y'8315''185''8776'ε'8658'x'8776'y_624
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.x≈y⇒x∙y⁻¹≈ε
d_x'8776'y'8658'x'8729'y'8315''185''8776'ε_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8776'y'8658'x'8729'y'8315''185''8776'ε_198 ~v0 ~v1 v2
  = du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_198 v2
du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_198 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_198 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_x'8776'y'8658'x'8729'y'8315''185''8776'ε_636
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.x≈z//y
d_x'8776'z'47''47'y_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8776'z'47''47'y_200 ~v0 ~v1 v2 = du_x'8776'z'47''47'y_200 v2
du_x'8776'z'47''47'y_200 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8776'z'47''47'y_200 v0
  = let v1
          = coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.QQuasigroup.du_x'8776'z'47''47'y_300
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_558 (coe v1)))
-- Algebra.Properties.AbelianGroup._.y≈x\\z
d_y'8776'x'92''92'z_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8776'x'92''92'z_202 ~v0 ~v1 v2 = du_y'8776'x'92''92'z_202 v2
du_y'8776'x'92''92'z_202 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8776'x'92''92'z_202 v0
  = let v1
          = coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.QQuasigroup.du_y'8776'x'92''92'z_284
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_558 (coe v1)))
-- Algebra.Properties.AbelianGroup._.ε⁻¹≈ε
d_ε'8315''185''8776'ε_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 -> AgdaAny
d_ε'8315''185''8776'ε_204 ~v0 ~v1 v2
  = du_ε'8315''185''8776'ε_204 v2
du_ε'8315''185''8776'ε_204 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 -> AgdaAny
du_ε'8315''185''8776'ε_204 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_ε'8315''185''8776'ε_608
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.⁻¹-anti-homo-//
d_'8315''185''45'anti'45'homo'45''47''47'_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'45''47''47'_206 ~v0 ~v1 v2
  = du_'8315''185''45'anti'45'homo'45''47''47'_206 v2
du_'8315''185''45'anti'45'homo'45''47''47'_206 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'45''47''47'_206 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'anti'45'homo'45''47''47'_660
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.⁻¹-anti-homo-\\
d_'8315''185''45'anti'45'homo'45''92''92'_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'45''92''92'_208 ~v0 ~v1 v2
  = du_'8315''185''45'anti'45'homo'45''92''92'_208 v2
du_'8315''185''45'anti'45'homo'45''92''92'_208 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'45''92''92'_208 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'anti'45'homo'45''92''92'_670
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.⁻¹-anti-homo-∙
d_'8315''185''45'anti'45'homo'45''8729'_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'45''8729'_210 ~v0 ~v1 v2
  = du_'8315''185''45'anti'45'homo'45''8729'_210 v2
du_'8315''185''45'anti'45'homo'45''8729'_210 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'45''8729'_210 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'anti'45'homo'45''8729'_650
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.⁻¹-injective
d_'8315''185''45'injective_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'injective_212 ~v0 ~v1 v2
  = du_'8315''185''45'injective_212 v2
du_'8315''185''45'injective_212 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'injective_212 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'injective_644
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.⁻¹-involutive
d_'8315''185''45'involutive_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny
d_'8315''185''45'involutive_214 ~v0 ~v1 v2
  = du_'8315''185''45'involutive_214 v2
du_'8315''185''45'involutive_214 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny
du_'8315''185''45'involutive_214 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'involutive_618
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.⁻¹-selfInverse
d_'8315''185''45'selfInverse_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'selfInverse_216 ~v0 ~v1 v2
  = du_'8315''185''45'selfInverse_216 v2
du_'8315''185''45'selfInverse_216 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'selfInverse_216 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'selfInverse_610
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup._.cancel
d_cancel_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cancel_218 ~v0 ~v1 v2 = du_cancel_218 v2
du_cancel_218 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cancel_218 v0
  = let v1
          = coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.QQuasigroup.du_cancel_276
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_558 (coe v1)))
-- Algebra.Properties.AbelianGroup._.cancelʳ
d_cancel'691'_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'691'_220 ~v0 ~v1 v2 = du_cancel'691'_220 v2
du_cancel'691'_220 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'691'_220 v0
  = let v1
          = coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.QQuasigroup.du_cancel'691'_266
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_558 (coe v1)))
-- Algebra.Properties.AbelianGroup._.cancelˡ
d_cancel'737'_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'737'_222 ~v0 ~v1 v2 = du_cancel'737'_222 v2
du_cancel'737'_222 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'737'_222 v0
  = let v1
          = coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Properties.QQuasigroup.du_cancel'737'_256
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_quasigroup_558 (coe v1)))
-- Algebra.Properties.AbelianGroup.⁻¹-anti-homo‿-
d_'8315''185''45'anti'45'homo'8255''45'_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'anti'45'homo'8255''45'_228 ~v0 ~v1 v2
  = du_'8315''185''45'anti'45'homo'8255''45'_228 v2
du_'8315''185''45'anti'45'homo'8255''45'_228 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'anti'45'homo'8255''45'_228 v0
  = coe
      MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'anti'45'homo'45''47''47'_660
      (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0))
-- Algebra.Properties.AbelianGroup.xyx⁻¹≈y
d_xyx'8315''185''8776'y_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_xyx'8315''185''8776'y_234 ~v0 ~v1 v2 v3 v4
  = du_xyx'8315''185''8776'y_234 v2 v3 v4
du_xyx'8315''185''8776'y_234 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_xyx'8315''185''8776'y_234 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v1 v2)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0 v1))
      v2
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3
                         = MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v3) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v1 v2)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0 v1))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v2 v1)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0 v1))
         v2
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                       (coe v6))))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v2 v1)
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0 v1))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v2
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v1
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0 v1)))
            v2
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v3
                               = MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0) in
                         coe
                           (let v4
                                  = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v3) in
                            coe
                              (let v5
                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                               coe
                                 (let v6
                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                            (coe v5) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                          (coe v6))))))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v2
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v1
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0 v1)))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v2
                  (MAlonzo.Code.Algebra.Bundles.d_ε_1660 (coe v0)))
               v2
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (let v3
                                  = MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0) in
                            coe
                              (let v4
                                     = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v3) in
                               coe
                                 (let v5
                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                                            (coe v4) in
                                  coe
                                    (let v6
                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                               (coe v5) in
                                     coe
                                       (coe
                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                          (coe
                                             MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                             (coe v6))))))))))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v2
                     (MAlonzo.Code.Algebra.Bundles.d_ε_1660 (coe v0)))
                  v2 v2
                  (let v3
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (let v3
                                       = MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664
                                           (coe v0) in
                                 coe
                                   (let v4
                                          = MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                                              (coe v3) in
                                    coe
                                      (let v5
                                             = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                                                 (coe v4) in
                                       coe
                                         (let v6
                                                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                                    (coe v5) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.du_setoid_200
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                                  (coe v6)))))))) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v3))
                        (coe v2)))
                  (let v3
                         = MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v3) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_identity'691'_728
                           (MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4)) v2))))
               (let v3
                      = MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                          (coe
                             MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0)) in
                coe
                  (let v4
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'737'_202
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                           (coe v2)
                           (coe
                              MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v1
                              (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0 v1))
                           (coe MAlonzo.Code.Algebra.Bundles.d_ε_1660 (coe v0))
                           (let v6
                                  = MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_inverse'691'_1108
                                 (MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v6)) v1)))))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_assoc_482
               (MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1050
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                        (coe
                           MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0)))))
               v2 v1
               (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0 v1)))
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                    (coe
                       MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0)) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'8729''45'cong'691'_206
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v5))
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0 v1)
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v1 v2)
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v2 v1)
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_comm_1146
                        (MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0)) v1
                        v2))))))
-- Algebra.Properties.AbelianGroup.⁻¹-∙-comm
d_'8315''185''45''8729''45'comm_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45''8729''45'comm_244 ~v0 ~v1 v2 v3 v4
  = du_'8315''185''45''8729''45'comm_244 v2 v3 v4
du_'8315''185''45''8729''45'comm_244 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1636 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45''8729''45'comm_244 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0 v1)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0 v2))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v1 v2))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v3
                         = MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0) in
                   coe
                     (let v4
                            = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v3) in
                      coe
                        (let v5
                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                         coe
                           (let v6
                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6))))))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v3
                      = MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0) in
                coe
                  (let v4
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v3) in
                   coe
                     (let v5
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                      coe
                        (let v6
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v6)))))))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0 v1)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0 v2))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v2 v1))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v1 v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v3
                            = MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0) in
                      coe
                        (let v4
                               = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v3) in
                         coe
                           (let v5
                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                            coe
                              (let v6
                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v5) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                    (coe
                                       MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                       (coe v6))))))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v2 v1))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v1 v2))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v1 v2))
            (let v3
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v3
                                 = MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0) in
                           coe
                             (let v4
                                    = MAlonzo.Code.Algebra.Structures.d_isGroup_1144 (coe v3) in
                              coe
                                (let v5
                                       = MAlonzo.Code.Algebra.Structures.d_isMonoid_1050 (coe v4) in
                                 coe
                                   (let v6
                                          = MAlonzo.Code.Algebra.Structures.d_isSemigroup_696
                                              (coe v5) in
                                    coe
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.du_setoid_200
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isMagma_480
                                            (coe v6)))))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v3))
                  (coe
                     MAlonzo.Code.Algebra.Bundles.d__'8315''185'_1662 v0
                     (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v1 v2))))
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1054
               (MAlonzo.Code.Algebra.Structures.d_isGroup_1144
                  (coe MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0)))
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v2 v1)
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__1658 v0 v1 v2)
               (coe
                  MAlonzo.Code.Algebra.Structures.d_comm_1146
                  (MAlonzo.Code.Algebra.Bundles.d_isAbelianGroup_1664 (coe v0)) v2
                  v1)))
         (coe
            MAlonzo.Code.Algebra.Properties.Group.du_'8315''185''45'anti'45'homo'45''8729'_650
            (coe MAlonzo.Code.Algebra.Bundles.du_group_1732 (coe v0)) (coe v2)
            (coe v1)))
