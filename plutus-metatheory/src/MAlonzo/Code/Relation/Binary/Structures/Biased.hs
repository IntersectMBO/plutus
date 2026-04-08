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

module MAlonzo.Code.Relation.Binary.Structures.Biased where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Consequences
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Relation.Binary.Structures.Biased._.IsEquivalence
d_IsEquivalence_46 a0 a1 a2 a3 = ()
-- Relation.Binary.Structures.Biased._.IsStrictTotalOrder
d_IsStrictTotalOrder_66 a0 a1 a2 a3 a4 a5 = ()
-- Relation.Binary.Structures.Biased._.IsEquivalence.refl
d_refl_356 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  AgdaAny -> AgdaAny
d_refl_356 v0
  = coe MAlonzo.Code.Relation.Binary.Structures.d_refl_36 (coe v0)
-- Relation.Binary.Structures.Biased._.IsEquivalence.sym
d_sym_360 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_360 v0
  = coe MAlonzo.Code.Relation.Binary.Structures.d_sym_38 (coe v0)
-- Relation.Binary.Structures.Biased._.IsEquivalence.trans
d_trans_362 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_362 v0
  = coe MAlonzo.Code.Relation.Binary.Structures.d_trans_40 (coe v0)
-- Relation.Binary.Structures.Biased._.IsStrictTotalOrder.compare
d_compare_484 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_484 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_compare_634 (coe v0)
-- Relation.Binary.Structures.Biased._.IsStrictTotalOrder.isStrictPartialOrder
d_isStrictPartialOrder_494 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_isStrictPartialOrder_494 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
      (coe v0)
-- Relation.Binary.Structures.Biased.IsStrictTotalOrderᶜ
d_IsStrictTotalOrder'7580'_604 a0 a1 a2 a3 a4 a5 = ()
data T_IsStrictTotalOrder'7580'_604
  = C_constructor_638 MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
                      (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                      (AgdaAny ->
                       AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158)
-- Relation.Binary.Structures.Biased.IsStrictTotalOrderᶜ.isEquivalence
d_isEquivalence_614 ::
  T_IsStrictTotalOrder'7580'_604 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_614 v0
  = case coe v0 of
      C_constructor_638 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.Biased.IsStrictTotalOrderᶜ.trans
d_trans_616 ::
  T_IsStrictTotalOrder'7580'_604 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_616 v0
  = case coe v0 of
      C_constructor_638 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.Biased.IsStrictTotalOrderᶜ.compare
d_compare_618 ::
  T_IsStrictTotalOrder'7580'_604 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_618 v0
  = case coe v0 of
      C_constructor_638 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.Biased.IsStrictTotalOrderᶜ.isStrictTotalOrderᶜ
d_isStrictTotalOrder'7580'_620 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder'7580'_604 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_isStrictTotalOrder'7580'_620 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isStrictTotalOrder'7580'_620 v6
du_isStrictTotalOrder'7580'_620 ::
  T_IsStrictTotalOrder'7580'_604 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
du_isStrictTotalOrder'7580'_620 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_680
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_412
         (d_isEquivalence_614 (coe v0)) (d_trans_616 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Consequences.du_trans'8743'tri'8658'resp_772
            (coe d_compare_618 (coe v0))))
      (coe d_compare_618 (coe v0))
