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

module MAlonzo.Code.Function.Metric.Nat.Definitions where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Function.Metric.Nat.Definitions.Congruent
d_Congruent_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_Congruent_14 = erased
-- Function.Metric.Nat.Definitions.Indiscernable
d_Indiscernable_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_Indiscernable_20 = erased
-- Function.Metric.Nat.Definitions.Definite
d_Definite_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_Definite_26 = erased
-- Function.Metric.Nat.Definitions.Symmetric
d_Symmetric_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_Symmetric_32 = erased
-- Function.Metric.Nat.Definitions.Bounded
d_Bounded_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_Bounded_34 = erased
-- Function.Metric.Nat.Definitions.TranslationInvariant
d_TranslationInvariant_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> Integer) -> ()
d_TranslationInvariant_36 = erased
-- Function.Metric.Nat.Definitions.TriangleInequality
d_TriangleInequality_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_TriangleInequality_38 = erased
-- Function.Metric.Nat.Definitions.MaxTriangleInequality
d_MaxTriangleInequality_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_MaxTriangleInequality_40 = erased
-- Function.Metric.Nat.Definitions.Contracting
d_Contracting_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_Contracting_42 = erased
-- Function.Metric.Nat.Definitions.ContractingOnOrbits
d_ContractingOnOrbits_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_ContractingOnOrbits_44 = erased
-- Function.Metric.Nat.Definitions.StrictlyContracting
d_StrictlyContracting_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_StrictlyContracting_46 = erased
-- Function.Metric.Nat.Definitions.StrictlyContractingOnOrbits
d_StrictlyContractingOnOrbits_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> Integer) -> ()
d_StrictlyContractingOnOrbits_50 = erased
