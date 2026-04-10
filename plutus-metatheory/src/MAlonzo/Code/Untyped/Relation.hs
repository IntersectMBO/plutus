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

module MAlonzo.Code.Untyped.Relation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Untyped

-- Untyped.Relation.Relation
d_Relation_4 :: ()
d_Relation_4 = erased
-- Untyped.Relation.Reflexive
d_Reflexive_8 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Reflexive_8 = erased
-- Untyped.Relation.Transitive
d_Transitive_16 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Transitive_16 = erased
-- Untyped.Relation.Symmetric
d_Symmetric_28 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Symmetric_28 = erased
-- Untyped.Relation.Idempotent
d_Idempotent_38 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Idempotent_38 = erased
-- Untyped.Relation.Transform
d_Transform_50 :: ()
d_Transform_50 = erased
-- Untyped.Relation.Transform₂
d_Transform'8322'_54 :: ()
d_Transform'8322'_54 = erased
-- Untyped.Relation.Compatible₁
d_Compatible'8321'_58 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  ()
d_Compatible'8321'_58 = erased
-- Untyped.Relation.Compatible₂
d_Compatible'8322'_70 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  ()
d_Compatible'8322'_70 = erased
-- Untyped.Relation.Compatible'
d_Compatible''_90 ::
  Integer ->
  Integer ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  ()
d_Compatible''_90 = erased
-- Untyped.Relation.Extensive
d_Extensive_100 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Extensive_100 = erased
-- Untyped.Relation.Extensive?
d_Extensive'63'_112 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Extensive'63'_112 = erased
-- Untyped.Relation._⊆_
d__'8838'__124 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d__'8838'__124 = erased
-- Untyped.Relation.ext?-⊆
d_ext'63''45''8838'_144 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_ext'63''45''8838'_144 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_ext'63''45''8838'_144 v3 v4 v5 v6 v7 v8
du_ext'63''45''8838'_144 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_ext'63''45''8838'_144 v0 v1 v2 v3 v4 v5
  = coe v0 v2 v3 v4 (coe v1 v2 v3 v4 v5)
-- Untyped.Relation.Equivalence
d_Equivalence_156 a0 = ()
data T_Equivalence_156
  = C_constructor_172 (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny -> AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny)
-- Untyped.Relation.Equivalence.refl
d_refl_166 ::
  T_Equivalence_156 ->
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny
d_refl_166 v0
  = case coe v0 of
      C_constructor_172 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Equivalence.trans
d_trans_168 ::
  T_Equivalence_156 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_168 v0
  = case coe v0 of
      C_constructor_172 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.Equivalence.sym
d_sym_170 ::
  T_Equivalence_156 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_sym_170 v0
  = case coe v0 of
      C_constructor_172 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible
d_TermCompatible_176 a0 = ()
data T_TermCompatible_176
  = C_constructor_296 (Integer ->
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
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
                       AgdaAny)
                      (Integer ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       MAlonzo.Code.Untyped.T__'8866'_14 ->
                       [MAlonzo.Code.Untyped.T__'8866'_14] ->
                       [MAlonzo.Code.Untyped.T__'8866'_14] ->
                       AgdaAny ->
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
                       AgdaAny)
                      (MAlonzo.Code.RawU.T_TmCon_202 -> Integer -> AgdaAny)
                      (Integer -> MAlonzo.Code.Builtin.T_Builtin_2 -> AgdaAny)
                      (Integer -> AgdaAny)
-- Untyped.Relation.TermCompatible.compat-var
d_compat'45'var_242 ::
  T_TermCompatible_176 ->
  Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_compat'45'var_242 v0
  = case coe v0 of
      C_constructor_296 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-ƛ
d_compat'45'ƛ_250 ::
  T_TermCompatible_176 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_compat'45'ƛ_250 v0
  = case coe v0 of
      C_constructor_296 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-·
d_compat'45''183'_252 ::
  T_TermCompatible_176 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny -> AgdaAny
d_compat'45''183'_252 v0
  = case coe v0 of
      C_constructor_296 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-force
d_compat'45'force_254 ::
  T_TermCompatible_176 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_compat'45'force_254 v0
  = case coe v0 of
      C_constructor_296 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-delay
d_compat'45'delay_256 ::
  T_TermCompatible_176 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_compat'45'delay_256 v0
  = case coe v0 of
      C_constructor_296 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-constr
d_compat'45'constr_266 ::
  T_TermCompatible_176 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  AgdaAny
d_compat'45'constr_266 v0
  = case coe v0 of
      C_constructor_296 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-case
d_compat'45'case_278 ::
  T_TermCompatible_176 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  AgdaAny
d_compat'45'case_278 v0
  = case coe v0 of
      C_constructor_296 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-con
d_compat'45'con_284 ::
  T_TermCompatible_176 ->
  MAlonzo.Code.RawU.T_TmCon_202 -> Integer -> AgdaAny
d_compat'45'con_284 v0
  = case coe v0 of
      C_constructor_296 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-builtin
d_compat'45'builtin_290 ::
  T_TermCompatible_176 ->
  Integer -> MAlonzo.Code.Builtin.T_Builtin_2 -> AgdaAny
d_compat'45'builtin_290 v0
  = case coe v0 of
      C_constructor_296 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-error
d_compat'45'error_294 :: T_TermCompatible_176 -> Integer -> AgdaAny
d_compat'45'error_294 v0
  = case coe v0 of
      C_constructor_296 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
