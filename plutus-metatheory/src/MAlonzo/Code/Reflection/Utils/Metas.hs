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

module MAlonzo.Code.Reflection.Utils.Metas where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Data.List.Base

-- Reflection.Utils.Metas.isMeta
d_isMeta_6 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> Bool
d_isMeta_6 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v2 v3
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Reflection.Utils.Metas.findMetas
d_findMetas_10 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154]
d_findMetas_10 = coe d_'46'extendedlambda1_16
-- Reflection.Utils.Metas.findMetas*
d_findMetas'42'_12 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154]
d_findMetas'42'_12 = coe d_'46'extendedlambda2_40
-- Reflection.Utils.Metas.findMetasCl
d_findMetasCl_14 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154]
d_findMetasCl_14 = coe d_'46'extendedlambda3_46
-- Reflection.Utils.Metas..extendedlambda1
d_'46'extendedlambda1_16 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154]
d_'46'extendedlambda1_16 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_var_172 v1 v2
        -> coe d_findMetas'42'_12 v2
      MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 v1 v2
        -> coe d_findMetas'42'_12 v2
      MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 v1 v2
        -> coe d_findMetas'42'_12 v2
      MAlonzo.Code.Agda.Builtin.Reflection.C_lam_190 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v3 v4
               -> coe d_findMetas_10 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196 v1 v2
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe d_findMetasCl_14 v1) (coe d_findMetas'42'_12 v2)
      MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v3 v4
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v5 v6
                      -> coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe d_findMetas_10 v4) (coe d_findMetas_10 v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Reflection.C_agda'45'sort_206 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Agda.Builtin.Reflection.C_lit_210 v1
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
             (coe d_findMetas'42'_12 v2)
      MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Metas..extendedlambda2
d_'46'extendedlambda2_40 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154]
d_'46'extendedlambda2_40 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v3 v4
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_findMetas_10 v4) (coe d_findMetas'42'_12 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Metas..extendedlambda3
d_'46'extendedlambda3_46 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154]
d_'46'extendedlambda3_46 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272 v3 v4 v5
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_findMetas_10 v5) (coe d_findMetasCl_14 v2)
             MAlonzo.Code.Agda.Builtin.Reflection.C_absurd'45'clause_278 v3 v4
               -> coe d_findMetasCl_14 v2
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
