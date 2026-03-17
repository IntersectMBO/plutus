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

module MAlonzo.Code.Reflection.Utils.Substitute where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base

-- Reflection.Utils.Substitute.Subst
d_Subst_6 :: () -> ()
d_Subst_6 = erased
-- Reflection.Utils.Substitute.substTerm
d_substTerm_10 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_substTerm_10 v0 v1
  = coe d_'46'extendedlambda0_24 (coe v0) (coe v1)
-- Reflection.Utils.Substitute.substArgs
d_substArgs_12 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_substArgs_12 v0 v1
  = coe d_'46'extendedlambda2_60 (coe v0) (coe v1)
-- Reflection.Utils.Substitute.substArg
d_substArg_14 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88
d_substArg_14 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v3)
             (coe d_substTerm_10 v0 v1 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Substitute.substAbs
d_substAbs_16 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112
d_substAbs_16 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 (coe v3)
             (coe d_substTerm_10 (addInt (coe (1 :: Integer)) (coe v0)) v1 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Substitute.substSort
d_substSort_18 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Sort_156 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Sort_156
d_substSort_18 v0 v1
  = coe d_'46'extendedlambda3_86 (coe v0) (coe v1)
-- Reflection.Utils.Substitute..extendedlambda0
d_'46'extendedlambda0_24 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_'46'extendedlambda0_24 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_var_172 v3 v4
        -> coe
             d_'46'extendedlambda1_30 (coe v0) (coe v1) (coe v3) (coe v4)
             (coe MAlonzo.Code.Data.Nat.Base.d_compare_470 (coe v0) (coe v3))
      MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 (coe v3)
             (coe d_substArgs_12 v0 v1 v4)
      MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 (coe v3)
             (coe d_substArgs_12 v0 v1 v4)
      MAlonzo.Code.Agda.Builtin.Reflection.C_lam_190 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_lam_190 (coe v3)
             (coe d_substAbs_16 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196 v3 v4
        -> coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216
      MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202
             (coe d_substArg_14 (coe v0) (coe v1) (coe v3))
             (coe d_substAbs_16 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Agda.Builtin.Reflection.C_agda'45'sort_206 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_agda'45'sort_206
             (coe d_substSort_18 v0 v1 v3)
      MAlonzo.Code.Agda.Builtin.Reflection.C_lit_210 v3 -> coe v2
      MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 (coe v3)
             (coe d_substArgs_12 v0 v1 v4)
      MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Substitute..extendedlambda1
d_'46'extendedlambda1_30 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Data.Nat.Base.T_Ordering_448 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_'46'extendedlambda1_30 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.Nat.Base.C_less_454 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_var_172
             (coe
                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                (addInt (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v6))
                (1 :: Integer))
             (coe d_substArgs_12 v0 v1 v3)
      MAlonzo.Code.Data.Nat.Base.C_equal_458 -> coe v1
      MAlonzo.Code.Data.Nat.Base.C_greater_464 v6
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_var_172 (coe v2)
             (coe
                d_substArgs_12
                (addInt (coe addInt (coe (1 :: Integer)) (coe v2)) (coe v6)) v1 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Substitute..extendedlambda2
d_'46'extendedlambda2_60 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_'46'extendedlambda2_60 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_substArg_14 (coe v0) (coe v1) (coe v3))
             (coe d_substArgs_12 v0 v1 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Substitute..extendedlambda3
d_'46'extendedlambda3_86 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Sort_156 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Sort_156
d_'46'extendedlambda3_86 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_set_220 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_set_220
             (coe d_substTerm_10 v0 v1 v3)
      MAlonzo.Code.Agda.Builtin.Reflection.C_lit_224 v3 -> coe v2
      MAlonzo.Code.Agda.Builtin.Reflection.C_prop_228 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_prop_228
             (coe d_substTerm_10 v0 v1 v3)
      MAlonzo.Code.Agda.Builtin.Reflection.C_propLit_232 v3 -> coe v2
      MAlonzo.Code.Agda.Builtin.Reflection.C_inf_236 v3 -> coe v2
      MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_238 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Substitute._._⁇_
d__'8263'__104 ::
  (Integer -> Integer) -> Integer -> Integer -> Integer
d__'8263'__104 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe v1) (coe v2))
      (coe v0 v2) (coe v2)
-- Reflection.Utils.Substitute._.mapFreeVars
d_mapFreeVars_110 ::
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_mapFreeVars_110 v0 v1
  = coe d_'46'extendedlambda4_128 (coe v0) (coe v1)
-- Reflection.Utils.Substitute._.mapFreeVars∗
d_mapFreeVars'8727'_112 ::
  (Integer -> Integer) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_mapFreeVars'8727'_112 v0 v1
  = coe d_'46'extendedlambda5_170 (coe v0) (coe v1)
-- Reflection.Utils.Substitute._.mapFreeVarsᵖ
d_mapFreeVars'7510'_114 ::
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158
d_mapFreeVars'7510'_114 v0 v1
  = coe d_'46'extendedlambda6_180 (coe v0) (coe v1)
-- Reflection.Utils.Substitute._.mapFreeVarsᵖ∗
d_mapFreeVars'7510''8727'_116 ::
  (Integer -> Integer) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_mapFreeVars'7510''8727'_116 v0 v1
  = coe d_'46'extendedlambda7_194 (coe v0) (coe v1)
-- Reflection.Utils.Substitute._.mapFreeVarsᵗ
d_mapFreeVars'7511'_118 ::
  (Integer -> Integer) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_mapFreeVars'7511'_118 v0 v1
  = coe d_'46'extendedlambda8_204 (coe v0) (coe v1)
-- Reflection.Utils.Substitute._.mapFreeVarsᶜ
d_mapFreeVars'7580'_120 ::
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160
d_mapFreeVars'7580'_120 v0 v1
  = coe d_'46'extendedlambda9_216 (coe v0) (coe v1)
-- Reflection.Utils.Substitute._.mapFreeVarsᶜ∗
d_mapFreeVars'7580''8727'_122 ::
  (Integer -> Integer) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160]
d_mapFreeVars'7580''8727'_122 v0 v1
  = coe d_'46'extendedlambda10_230 (coe v0) (coe v1)
-- Reflection.Utils.Substitute._.mapFreeVarsˢ
d_mapFreeVars'738'_124 ::
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Sort_156 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Sort_156
d_mapFreeVars'738'_124 v0 v1
  = coe d_'46'extendedlambda11_238 (coe v0) (coe v1)
-- Reflection.Utils.Substitute._..extendedlambda4
d_'46'extendedlambda4_128 ::
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_'46'extendedlambda4_128 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_var_172 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_var_172
             (coe d__'8263'__104 (coe v0) (coe v1) (coe v3))
             (coe d_mapFreeVars'8727'_112 v0 v1 v4)
      MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 (coe v3)
             (coe d_mapFreeVars'8727'_112 v0 v1 v4)
      MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 (coe v3)
             (coe d_mapFreeVars'8727'_112 v0 v1 v4)
      MAlonzo.Code.Agda.Builtin.Reflection.C_lam_190 v3 v4
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Reflection.C_lam_190 (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 (coe v5)
                       (coe
                          d_mapFreeVars_110 v0 (addInt (coe (1 :: Integer)) (coe v1)) v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196
             (coe d_mapFreeVars'7580''8727'_122 v0 v1 v3)
             (coe d_mapFreeVars'8727'_112 v0 v1 v4)
      MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v5 v6
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v7 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202
                           (coe
                              MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v5)
                              (coe d_mapFreeVars_110 v0 v1 v6))
                           (coe
                              MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 (coe v7)
                              (coe
                                 d_mapFreeVars_110 v0 (addInt (coe (1 :: Integer)) (coe v1)) v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Reflection.C_agda'45'sort_206 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_agda'45'sort_206
             (coe d_mapFreeVars'738'_124 v0 v1 v3)
      MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 (coe v3)
             (coe d_mapFreeVars'8727'_112 v0 v1 v4)
      _ -> coe v2
-- Reflection.Utils.Substitute._..extendedlambda5
d_'46'extendedlambda5_170 ::
  (Integer -> Integer) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_'46'extendedlambda5_170 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v5)
                       (coe d_mapFreeVars_110 v0 v1 v6))
                    (coe d_mapFreeVars'8727'_112 v0 v1 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Substitute._..extendedlambda6
d_'46'extendedlambda6_180 ::
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158
d_'46'extendedlambda6_180 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 (coe v3)
             (coe d_mapFreeVars'7510''8727'_116 v0 v1 v4)
      MAlonzo.Code.Agda.Builtin.Reflection.C_dot_248 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_dot_248
             (coe d_mapFreeVars_110 v0 v1 v3)
      MAlonzo.Code.Agda.Builtin.Reflection.C_absurd_264 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_absurd_264
             (coe d__'8263'__104 (coe v0) (coe v1) (coe v3))
      _ -> coe v2
-- Reflection.Utils.Substitute._..extendedlambda7
d_'46'extendedlambda7_194 ::
  (Integer -> Integer) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_'46'extendedlambda7_194 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v5)
                       (coe d_mapFreeVars'7510'_114 v0 v1 v6))
                    (coe
                       d_mapFreeVars'7510''8727'_116 v0
                       (addInt (coe (1 :: Integer)) (coe v1)) v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Substitute._..extendedlambda8
d_'46'extendedlambda8_204 ::
  (Integer -> Integer) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_'46'extendedlambda8_204 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v7 v8
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v7)
                                 (coe d_mapFreeVars_110 v0 v1 v8)))
                           (coe
                              d_mapFreeVars'7511'_118 v0 (addInt (coe (1 :: Integer)) (coe v1))
                              v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Substitute._..extendedlambda9
d_'46'extendedlambda9_216 ::
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160
d_'46'extendedlambda9_216 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272 v3 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
             (coe d_mapFreeVars'7511'_118 v0 v1 v3)
             (coe d_mapFreeVars'7510''8727'_116 v0 v1 v4)
             (coe
                d_mapFreeVars_110 v0
                (addInt
                   (coe MAlonzo.Code.Data.List.Base.du_length_268 v3) (coe v1))
                v5)
      MAlonzo.Code.Agda.Builtin.Reflection.C_absurd'45'clause_278 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_absurd'45'clause_278
             (coe d_mapFreeVars'7511'_118 v0 v1 v3)
             (coe d_mapFreeVars'7510''8727'_116 v0 v1 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Substitute._..extendedlambda10
d_'46'extendedlambda10_230 ::
  (Integer -> Integer) ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160]
d_'46'extendedlambda10_230 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d_mapFreeVars'7580'_120 v0 v1 v3)
             (coe d_mapFreeVars'7580''8727'_122 v0 v1 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Substitute._..extendedlambda11
d_'46'extendedlambda11_238 ::
  (Integer -> Integer) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Sort_156 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Sort_156
d_'46'extendedlambda11_238 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_set_220 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_set_220
             (coe d_mapFreeVars_110 v0 v1 v3)
      MAlonzo.Code.Agda.Builtin.Reflection.C_prop_228 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_prop_228
             (coe d_mapFreeVars_110 v0 v1 v3)
      _ -> coe v2
-- Reflection.Utils.Substitute._.mapVars
d_mapVars_246 ::
  (Integer -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_mapVars_246 v0
  = coe d_mapFreeVars_110 (coe v0) (coe (0 :: Integer))
-- Reflection.Utils.Substitute.varsToUnknown
d_varsToUnknown_248 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_varsToUnknown_248 = coe d_'46'extendedlambda4_252
-- Reflection.Utils.Substitute.varsToUnknown*
d_varsToUnknown'42'_250 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_varsToUnknown'42'_250 = coe d_'46'extendedlambda5_264
-- Reflection.Utils.Substitute..extendedlambda4
d_'46'extendedlambda4_252 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_'46'extendedlambda4_252 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_var_172 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216
      MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 (coe v1)
             (coe d_varsToUnknown'42'_250 v2)
      MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 (coe v1)
             (coe d_varsToUnknown'42'_250 v2)
      _ -> coe v0
-- Reflection.Utils.Substitute..extendedlambda5
d_'46'extendedlambda5_264 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_'46'extendedlambda5_264 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v3)
                       (coe d_varsToUnknown_248 v4))
                    (coe d_varsToUnknown'42'_250 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Substitute.mapVariables
d_mapVariables_272 ::
  (Integer -> Integer) ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158
d_mapVariables_272 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 (coe v2)
             (coe du_go_288 (coe v0) (coe v3))
      MAlonzo.Code.Agda.Builtin.Reflection.C_var_252 v2
        -> coe MAlonzo.Code.Agda.Builtin.Reflection.C_var_252 (coe v0 v2)
      _ -> coe v1
-- Reflection.Utils.Substitute._.go
d_go_288 ::
  (Integer -> Integer) ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_go_288 v0 ~v1 ~v2 v3 = du_go_288 v0 v3
du_go_288 ::
  (Integer -> Integer) ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
du_go_288 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v4)
                       (coe d_mapVariables_272 (coe v0) (coe v5)))
                    (coe du_go_288 (coe v0) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
