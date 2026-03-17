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

module MAlonzo.Code.Reflection.Utils.Records where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Reflection.AST.Name

-- Reflection.Utils.Records.mkRecord
d_mkRecord_6 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_mkRecord_6 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                 (coe
                    MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                    (coe
                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                       (coe
                          MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                          (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                             (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                             (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Reflection.C_proj_260
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1)))))
                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1))))
         (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Reflection.Utils.Records.updateField
d_updateField_16 ::
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_updateField_16 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v4 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                 (coe
                    MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                    (coe
                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                       (coe
                          MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                          (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                             (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                             (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                       (coe MAlonzo.Code.Agda.Builtin.Reflection.C_proj_260 (coe v4))))
                 (coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe
                       MAlonzo.Code.Class.DecEq.Core.du__'61''61'__18 (coe ())
                       (coe
                          MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
                          (coe MAlonzo.Code.Reflection.AST.Name.d__'8799'__12))
                       (coe v4) (coe v2))
                    (coe v3)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                             (coe
                                MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                   (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                   (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                             (coe v1))
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
         (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
