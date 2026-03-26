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
-- Untyped.Relation.idemp-trans
d_idemp'45'trans_52 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny -> AgdaAny
d_idemp'45'trans_52 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_idemp'45'trans_52 v6
du_idemp'45'trans_52 :: AgdaAny -> AgdaAny
du_idemp'45'trans_52 v0 = coe v0
-- Untyped.Relation.Transform
d_Transform_70 :: ()
d_Transform_70 = erased
-- Untyped.Relation.Transform₂
d_Transform'8322'_74 :: ()
d_Transform'8322'_74 = erased
-- Untyped.Relation.Compatible₁
d_Compatible'8321'_78 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  ()
d_Compatible'8321'_78 = erased
-- Untyped.Relation.Compatible₂
d_Compatible'8322'_90 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  ()
d_Compatible'8322'_90 = erased
-- Untyped.Relation.Extensive
d_Extensive_106 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_Extensive_106 = erased
-- Untyped.Relation.TermCompatible
d_TermCompatible_118 a0 = ()
data T_TermCompatible_118
  = C_constructor_238 (Integer ->
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
d_compat'45'var_184 ::
  T_TermCompatible_118 ->
  Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_compat'45'var_184 v0
  = case coe v0 of
      C_constructor_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-ƛ
d_compat'45'ƛ_192 ::
  T_TermCompatible_118 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_compat'45'ƛ_192 v0
  = case coe v0 of
      C_constructor_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-·
d_compat'45''183'_194 ::
  T_TermCompatible_118 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny -> AgdaAny
d_compat'45''183'_194 v0
  = case coe v0 of
      C_constructor_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-force
d_compat'45'force_196 ::
  T_TermCompatible_118 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_compat'45'force_196 v0
  = case coe v0 of
      C_constructor_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-delay
d_compat'45'delay_198 ::
  T_TermCompatible_118 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny -> AgdaAny
d_compat'45'delay_198 v0
  = case coe v0 of
      C_constructor_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-constr
d_compat'45'constr_208 ::
  T_TermCompatible_118 ->
  Integer ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  AgdaAny
d_compat'45'constr_208 v0
  = case coe v0 of
      C_constructor_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-case
d_compat'45'case_220 ::
  T_TermCompatible_118 ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  AgdaAny
d_compat'45'case_220 v0
  = case coe v0 of
      C_constructor_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-con
d_compat'45'con_226 ::
  T_TermCompatible_118 ->
  MAlonzo.Code.RawU.T_TmCon_202 -> Integer -> AgdaAny
d_compat'45'con_226 v0
  = case coe v0 of
      C_constructor_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-builtin
d_compat'45'builtin_232 ::
  T_TermCompatible_118 ->
  Integer -> MAlonzo.Code.Builtin.T_Builtin_2 -> AgdaAny
d_compat'45'builtin_232 v0
  = case coe v0 of
      C_constructor_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Relation.TermCompatible.compat-error
d_compat'45'error_236 :: T_TermCompatible_118 -> Integer -> AgdaAny
d_compat'45'error_236 v0
  = case coe v0 of
      C_constructor_238 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
