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

module MAlonzo.Code.Untyped.Relation.Binary.Structures where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Relation.Binary.Core

-- Untyped.Relation.Binary.Structures.Equivalence
d_Equivalence_10 a0 = ()
data T_Equivalence_10
  = C_constructor_26 (Integer ->
                      MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny)
                     (Integer ->
                      MAlonzo.Code.Untyped.T__'8866'_14 ->
                      MAlonzo.Code.Untyped.T__'8866'_14 ->
                      MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny -> AgdaAny)
                     (Integer ->
                      MAlonzo.Code.Untyped.T__'8866'_14 ->
                      MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny)
-- Untyped.Relation.Binary.Structures.Equivalence.~-refl
d_'126''45'refl_20 ::
  T_Equivalence_10 ->
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny
d_'126''45'refl_20 v0
  = case coe v0 of
      C_constructor_26 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Binary.Structures.Equivalence.~-trans
d_'126''45'trans_22 ::
  T_Equivalence_10 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny -> AgdaAny
d_'126''45'trans_22 v0
  = case coe v0 of
      C_constructor_26 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Binary.Structures.Equivalence.~-sym
d_'126''45'sym_24 ::
  T_Equivalence_10 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_'126''45'sym_24 v0
  = case coe v0 of
      C_constructor_26 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Binary.Structures.TermCompatible
d_TermCompatible_30 a0 = ()
data T_TermCompatible_30
  = C_constructor_150 (Integer ->
                       MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny -> AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny)
                      (Integer ->
                       Integer ->
                       [MAlonzo.Code.Untyped.T__'8866'_14] ->
                       [MAlonzo.Code.Untyped.T__'8866'_14] ->
                       MAlonzo.Code.Untyped.Relation.Binary.Core.T_Pointwise_20 ->
                       AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       [MAlonzo.Code.Untyped.T__'8866'_14] ->
                       [MAlonzo.Code.Untyped.T__'8866'_14] ->
                       AgdaAny ->
                       MAlonzo.Code.Untyped.Relation.Binary.Core.T_Pointwise_20 ->
                       AgdaAny)
                      (MAlonzo.Code.RawU.T_TmCon_204 -> Integer -> AgdaAny)
                      (Integer -> MAlonzo.Code.Builtin.T_Builtin_2 -> AgdaAny)
                      (Integer -> AgdaAny)
-- Untyped.Relation.Binary.Structures.TermCompatible.compat-var
d_compat'45'var_96 ::
  T_TermCompatible_30 ->
  Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_compat'45'var_96 v0
  = case coe v0 of
      C_constructor_150 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Binary.Structures.TermCompatible.compat-ƛ
d_compat'45'ƛ_104 ::
  T_TermCompatible_30 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_compat'45'ƛ_104 v0
  = case coe v0 of
      C_constructor_150 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Binary.Structures.TermCompatible.compat-·
d_compat'45''183'_106 ::
  T_TermCompatible_30 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny -> AgdaAny
d_compat'45''183'_106 v0
  = case coe v0 of
      C_constructor_150 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Binary.Structures.TermCompatible.compat-force
d_compat'45'force_108 ::
  T_TermCompatible_30 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_compat'45'force_108 v0
  = case coe v0 of
      C_constructor_150 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Binary.Structures.TermCompatible.compat-delay
d_compat'45'delay_110 ::
  T_TermCompatible_30 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_compat'45'delay_110 v0
  = case coe v0 of
      C_constructor_150 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Binary.Structures.TermCompatible.compat-constr
d_compat'45'constr_120 ::
  T_TermCompatible_30 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.Relation.Binary.Core.T_Pointwise_20 -> AgdaAny
d_compat'45'constr_120 v0
  = case coe v0 of
      C_constructor_150 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Binary.Structures.TermCompatible.compat-case
d_compat'45'case_132 ::
  T_TermCompatible_30 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  AgdaAny ->
  MAlonzo.Code.Untyped.Relation.Binary.Core.T_Pointwise_20 -> AgdaAny
d_compat'45'case_132 v0
  = case coe v0 of
      C_constructor_150 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Binary.Structures.TermCompatible.compat-con
d_compat'45'con_138 ::
  T_TermCompatible_30 ->
  MAlonzo.Code.RawU.T_TmCon_204 -> Integer -> AgdaAny
d_compat'45'con_138 v0
  = case coe v0 of
      C_constructor_150 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Binary.Structures.TermCompatible.compat-builtin
d_compat'45'builtin_144 ::
  T_TermCompatible_30 ->
  Integer -> MAlonzo.Code.Builtin.T_Builtin_2 -> AgdaAny
d_compat'45'builtin_144 v0
  = case coe v0 of
      C_constructor_150 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Binary.Structures.TermCompatible.compat-error
d_compat'45'error_148 :: T_TermCompatible_30 -> Integer -> AgdaAny
d_compat'45'error_148 v0
  = case coe v0 of
      C_constructor_150 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
