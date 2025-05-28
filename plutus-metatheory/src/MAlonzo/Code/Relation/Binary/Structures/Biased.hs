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

module MAlonzo.Code.Relation.Binary.Structures.Biased where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Relation.Binary.Consequences qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Structures.Biased._.IsEquivalence
d_IsEquivalence_30 a0 a1 a2 a3 = ()
-- Relation.Binary.Structures.Biased._.IsStrictTotalOrder
d_IsStrictTotalOrder_40 a0 a1 a2 a3 a4 a5 = ()
-- Relation.Binary.Structures.Biased._.IsEquivalence.refl
d_refl_274 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  AgdaAny -> AgdaAny
d_refl_274 v0
  = coe MAlonzo.Code.Relation.Binary.Structures.d_refl_34 (coe v0)
-- Relation.Binary.Structures.Biased._.IsEquivalence.sym
d_sym_278 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_278 v0
  = coe MAlonzo.Code.Relation.Binary.Structures.d_sym_36 (coe v0)
-- Relation.Binary.Structures.Biased._.IsEquivalence.trans
d_trans_280 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_280 v0
  = coe MAlonzo.Code.Relation.Binary.Structures.d_trans_38 (coe v0)
-- Relation.Binary.Structures.Biased._.IsStrictTotalOrder.compare
d_compare_402 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_402 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_compare_544 (coe v0)
-- Relation.Binary.Structures.Biased._.IsStrictTotalOrder.isStrictPartialOrder
d_isStrictPartialOrder_412 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_isStrictPartialOrder_412 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
      (coe v0)
-- Relation.Binary.Structures.Biased.IsStrictTotalOrderᶜ
d_IsStrictTotalOrder'7580'_522 a0 a1 a2 a3 a4 a5 = ()
data T_IsStrictTotalOrder'7580'_522
  = C_IsStrictTotalOrder'7580''46'constructor_6029 MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
                                                   (AgdaAny ->
                                                    AgdaAny ->
                                                    AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
                                                   (AgdaAny ->
                                                    AgdaAny ->
                                                    MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158)
-- Relation.Binary.Structures.Biased.IsStrictTotalOrderᶜ.isEquivalence
d_isEquivalence_532 ::
  T_IsStrictTotalOrder'7580'_522 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_532 v0
  = case coe v0 of
      C_IsStrictTotalOrder'7580''46'constructor_6029 v1 v2 v3 -> coe v1
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.Biased.IsStrictTotalOrderᶜ.trans
d_trans_534 ::
  T_IsStrictTotalOrder'7580'_522 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_534 v0
  = case coe v0 of
      C_IsStrictTotalOrder'7580''46'constructor_6029 v1 v2 v3 -> coe v2
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.Biased.IsStrictTotalOrderᶜ.compare
d_compare_536 ::
  T_IsStrictTotalOrder'7580'_522 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_536 v0
  = case coe v0 of
      C_IsStrictTotalOrder'7580''46'constructor_6029 v1 v2 v3 -> coe v3
      _                                                       -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Structures.Biased.IsStrictTotalOrderᶜ.isStrictTotalOrderᶜ
d_isStrictTotalOrder'7580'_538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IsStrictTotalOrder'7580'_522 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_isStrictTotalOrder'7580'_538 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isStrictTotalOrder'7580'_538 v6
du_isStrictTotalOrder'7580'_538 ::
  T_IsStrictTotalOrder'7580'_522 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
du_isStrictTotalOrder'7580'_538 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_24953
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_14045
         (d_isEquivalence_532 (coe v0)) (d_trans_534 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Consequences.du_trans'8743'tri'8658'resp_716
            (coe d_compare_536 (coe v0))))
      (coe d_compare_536 (coe v0))
