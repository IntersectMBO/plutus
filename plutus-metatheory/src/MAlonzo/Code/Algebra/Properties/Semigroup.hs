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

module MAlonzo.Code.Algebra.Properties.Semigroup where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Properties.Semigroup._.Alternative
d_Alternative_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Alternative_74 = erased
-- Algebra.Properties.Semigroup._.Flexible
d_Flexible_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Flexible_88 = erased
-- Algebra.Properties.Semigroup._.LeftAlternative
d_LeftAlternative_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftAlternative_106 = erased
-- Algebra.Properties.Semigroup._.RightAlternative
d_RightAlternative_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightAlternative_136 = erased
-- Algebra.Properties.Semigroup.x∙yz≈xy∙z
d_x'8729'yz'8776'xy'8729'z_188 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'yz'8776'xy'8729'z_188 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_556 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__554 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__554 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__554 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__554 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_556 (coe v0)) v1 v2 v3)
-- Algebra.Properties.Semigroup.alternativeˡ
d_alternative'737'_196 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_alternative'737'_196 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_482
      (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_556 (coe v0)) v1 v1 v2
-- Algebra.Properties.Semigroup.alternativeʳ
d_alternative'691'_202 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_alternative'691'_202 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_480
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_556 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__554 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__554 v0 v1 v2) v2)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__554 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__554 v0 v2 v2))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_482
         (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_556 (coe v0)) v1 v2 v2)
-- Algebra.Properties.Semigroup.alternative
d_alternative_208 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alternative_208 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Structures.d_assoc_482
              (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_556 (coe v0)) v1 v1
              v2))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_sym_36
              (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                 (coe
                    MAlonzo.Code.Algebra.Structures.d_isMagma_480
                    (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_556 (coe v0))))
              (coe
                 MAlonzo.Code.Algebra.Bundles.d__'8729'__554 v0
                 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__554 v0 v1 v2) v2)
              (coe
                 MAlonzo.Code.Algebra.Bundles.d__'8729'__554 v0 v1
                 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__554 v0 v2 v2))
              (coe
                 MAlonzo.Code.Algebra.Structures.d_assoc_482
                 (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_556 (coe v0)) v1 v2
                 v2)))
-- Algebra.Properties.Semigroup.flexible
d_flexible_210 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_flexible_210 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_482
      (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_556 (coe v0)) v1 v2 v1
