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

module MAlonzo.Code.Reflection.Utils.Args where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Reflection.AST.Argument
import qualified MAlonzo.Code.Reflection.AST.Argument.Information
import qualified MAlonzo.Code.Reflection.AST.Argument.Visibility
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Reflection.Utils.Args.getVisibility
d_getVisibility_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48
d_getVisibility_6 ~v0 ~v1 v2 = du_getVisibility_6 v2
du_getVisibility_6 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48
du_getVisibility_6 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82 v3 v4
               -> coe v3
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Args.unArgs
d_unArgs_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> [AgdaAny]
d_unArgs_10 ~v0 ~v1 = du_unArgs_10
du_unArgs_10 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> [AgdaAny]
du_unArgs_10
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe MAlonzo.Code.Reflection.AST.Argument.du_unArg_74)
-- Reflection.Utils.Args.args
d_args_12 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_args_12 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_var_172 v2 v3 -> coe v3
         MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 v2 v3 -> coe v3
         MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 v2 v3 -> coe v3
         _ -> coe v1)
-- Reflection.Utils.Args.args′
d_args'8242'_22 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154]
d_args'8242'_22 v0 = coe du_unArgs_10 (d_args_12 (coe v0))
-- Reflection.Utils.Args.vArgs
d_vArgs_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> [AgdaAny]
d_vArgs_24 v0 ~v1 = du_vArgs_24 v0
du_vArgs_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> [AgdaAny]
du_vArgs_24 v0 = coe du_'46'extendedlambda1_26 (coe v0)
-- Reflection.Utils.Args..extendedlambda1
d_'46'extendedlambda1_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> [AgdaAny]
d_'46'extendedlambda1_26 v0 ~v1 v2
  = du_'46'extendedlambda1_26 v0 v2
du_'46'extendedlambda1_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> [AgdaAny]
du_'46'extendedlambda1_26 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v4 v5
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82 v6 v7
                      -> let v8 = coe du_vArgs_24 v0 v3 in
                         coe
                           (case coe v6 of
                              MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50
                                -> case coe v7 of
                                     MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74 v9 v10
                                       -> case coe v9 of
                                            MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58
                                              -> case coe v10 of
                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66
                                                     -> coe
                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                          (coe v5) (coe du_vArgs_24 v0 v3)
                                                   _ -> coe v8
                                            _ -> coe v8
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v8)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Args.argInfo
d_argInfo_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_ArgInfo_76
d_argInfo_34 ~v0 ~v1 v2 = du_argInfo_34 v2
du_argInfo_34 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_ArgInfo_76
du_argInfo_34 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Args.isVisible?
d_isVisible'63'_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isVisible'63'_40 ~v0 ~v1 v2 = du_isVisible'63'_40 v2
du_isVisible'63'_40 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_isVisible'63'_40 v0
  = coe
      MAlonzo.Code.Reflection.AST.Argument.Visibility.d__'8799'__8
      (coe
         MAlonzo.Code.Reflection.AST.Argument.Information.d_visibility_16
         (coe du_argInfo_34 (coe v0)))
      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
-- Reflection.Utils.Args.isInstance?
d_isInstance'63'_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isInstance'63'_46 ~v0 ~v1 v2 = du_isInstance'63'_46 v2
du_isInstance'63'_46 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_isInstance'63'_46 v0
  = coe
      MAlonzo.Code.Reflection.AST.Argument.Visibility.d__'8799'__8
      (coe
         MAlonzo.Code.Reflection.AST.Argument.Information.d_visibility_16
         (coe du_argInfo_34 (coe v0)))
      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_instance'8242'_54)
-- Reflection.Utils.Args.isHidden?
d_isHidden'63'_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_isHidden'63'_52 ~v0 ~v1 v2 = du_isHidden'63'_52 v2
du_isHidden'63'_52 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_isHidden'63'_52 v0
  = coe
      MAlonzo.Code.Reflection.AST.Argument.Visibility.d__'8799'__8
      (coe
         MAlonzo.Code.Reflection.AST.Argument.Information.d_visibility_16
         (coe du_argInfo_34 (coe v0)))
      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_hidden_52)
-- Reflection.Utils.Args.remove-iArgs
d_remove'45'iArgs_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_remove'45'iArgs_56 ~v0 ~v1 v2 = du_remove'45'iArgs_56 v2
du_remove'45'iArgs_56 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
du_remove'45'iArgs_56 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82 v5 v6
                      -> let v7
                               = coe
                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                                   (coe du_remove'45'iArgs_56 (coe v2)) in
                         coe
                           (case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Reflection.C_instance'8242'_54
                                -> case coe v6 of
                                     MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74 v8 v9
                                       -> case coe v8 of
                                            MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58
                                              -> case coe v9 of
                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66
                                                     -> coe du_remove'45'iArgs_56 (coe v2)
                                                   _ -> coe v7
                                            _ -> coe v7
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> coe v7)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Args.hide
d_hide_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88
d_hide_66 ~v0 ~v1 v2 = du_hide_66 v2
du_hide_66 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88
du_hide_66 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82 v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50
                      -> case coe v4 of
                           MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74 v5 v6
                             -> case coe v5 of
                                  MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58
                                    -> case coe v6 of
                                         MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_hidden_52)
                                                   (coe v4))
                                                (coe v2)
                                         _ -> coe v0
                                  _ -> coe v0
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Reflection.C_hidden_52
                      -> case coe v4 of
                           MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74 v5 v6
                             -> case coe v5 of
                                  MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58
                                    -> coe seq (coe v6) (coe v0)
                                  _ -> coe v0
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Agda.Builtin.Reflection.C_instance'8242'_54
                      -> case coe v4 of
                           MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74 v5 v6
                             -> case coe v5 of
                                  MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58
                                    -> coe seq (coe v6) (coe v0)
                                  _ -> coe v0
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Args.∀indices⋯
d_'8704'indices'8943'_78 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_'8704'indices'8943'_78 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202
             (coe du_hide_66 (coe v2))
             (coe
                MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122
                (coe ("_" :: Data.Text.Text))
                (coe d_'8704'indices'8943'_78 (coe v3) (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Args.apply⋯
d_apply'8943'_88 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_apply'8943'_88 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 (coe v1)
      (coe
         du_remove'45'iArgs_56
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe
               (\ v2 ->
                  case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                      -> case coe v4 of
                           MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v5 v6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v5)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Reflection.C_var_172
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                        (coe MAlonzo.Code.Data.List.Base.du_length_268 v0)
                                        (addInt
                                           (coe (1 :: Integer))
                                           (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v3))))
                                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError))
            (coe
               MAlonzo.Code.Data.List.Base.du_zip_182
               (MAlonzo.Code.Data.List.Base.d_allFin_408
                  (coe MAlonzo.Code.Data.List.Base.du_length_268 v0))
               v0)))
-- Reflection.Utils.Args.apply∗
d_apply'8727'_100 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_apply'8727'_100 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_var_172 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_var_172 (coe v2)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3) (coe v1))
      MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 (coe v2)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3) (coe v1))
      MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 (coe v2)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3) (coe v1))
      MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196 (coe v2)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3) (coe v1))
      MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 (coe v2)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3) (coe v1))
      _ -> coe v0
