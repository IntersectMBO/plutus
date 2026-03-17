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

module MAlonzo.Code.Reflection.Utils.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Reflection.AST.Abstraction
import qualified MAlonzo.Code.Reflection.AST.Argument

-- Reflection.Utils.Core.absName
d_absName_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_absName_6 ~v0 ~v1 v2 = du_absName_6 v2
du_absName_6 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_absName_6 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Core.tyName
d_tyName_12 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> Maybe AgdaAny
d_tyName_12 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 v2 v3
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
         MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 v2 v3
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
         _ -> coe v1)
-- Reflection.Utils.Core.TypeView
d_TypeView_20 :: ()
d_TypeView_20 = erased
-- Reflection.Utils.Core.viewTy
d_viewTy_22 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_viewTy_22 v0
  = let v1
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v0) in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202 v2 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v4 v5
                  -> coe
                       MAlonzo.Code.Data.Product.Base.du_map'8321'_138
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe
                             MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 (coe v4) (coe v2)))
                       (d_viewTy_22 (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Reflection.Utils.Core.tyView
d_tyView_34 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_tyView_34 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             [] -> coe v2
             (:) v3 v4
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v5 v6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202 (coe v6)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 (coe v5)
                              (coe
                                 d_tyView_34
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v2))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Core.argumentWise
d_argumentWise_46 ::
  (MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
   MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154) ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_argumentWise_46 v0 v1
  = coe
      d_tyView_34
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe
               MAlonzo.Code.Reflection.AST.Abstraction.du_map_22
               (coe MAlonzo.Code.Reflection.AST.Argument.du_map_54 (coe v0)))
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe d_viewTy_22 (coe v1))))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe d_viewTy_22 (coe v1))))
-- Reflection.Utils.Core.viewTy′
d_viewTy'8242'_58 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_viewTy'8242'_58 v0
  = let v1
          = coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v0) in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202 v2 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v4 v5
                  -> coe
                       MAlonzo.Code.Data.Product.Base.du_map'8321'_138
                       (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2))
                       (d_viewTy'8242'_58 (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Reflection.Utils.Core.argTys
d_argTys_68 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_argTys_68 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe d_viewTy'8242'_58 (coe v0))
-- Reflection.Utils.Core.resultTy
d_resultTy_70 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_resultTy_70 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe d_viewTy'8242'_58 (coe v0))
-- Reflection.Utils.Core.tyTele
d_tyTele_72 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_tyTele_72 = coe d_'46'extendedlambda1_74
-- Reflection.Utils.Core..extendedlambda1
d_'46'extendedlambda1_74 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_'46'extendedlambda1_74 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202 v2 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v2))
                       (coe d_tyTele_72 v5)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v1)
-- Reflection.Utils.Core.DataDef
d_DataDef_82 = ()
data T_DataDef_82
  = C_DataDef'46'constructor_2729 AgdaAny
                                  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                                  [MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112]
                                  [MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112]
-- Reflection.Utils.Core.DataDef.name
d_name_92 :: T_DataDef_82 -> AgdaAny
d_name_92 v0
  = case coe v0 of
      C_DataDef'46'constructor_2729 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Core.DataDef.constructors
d_constructors_94 ::
  T_DataDef_82 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_constructors_94 v0
  = case coe v0 of
      C_DataDef'46'constructor_2729 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Core.DataDef.params
d_params_96 ::
  T_DataDef_82 -> [MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112]
d_params_96 v0
  = case coe v0 of
      C_DataDef'46'constructor_2729 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Core.DataDef.indices
d_indices_98 ::
  T_DataDef_82 -> [MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112]
d_indices_98 v0
  = case coe v0 of
      C_DataDef'46'constructor_2729 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Core.RecordDef
d_RecordDef_100 = ()
data T_RecordDef_100
  = C_RecordDef'46'constructor_2859 AgdaAny
                                    [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
                                    [MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112]
-- Reflection.Utils.Core.RecordDef.name
d_name_108 :: T_RecordDef_100 -> AgdaAny
d_name_108 v0
  = case coe v0 of
      C_RecordDef'46'constructor_2859 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Core.RecordDef.fields
d_fields_110 ::
  T_RecordDef_100 -> [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_fields_110 v0
  = case coe v0 of
      C_RecordDef'46'constructor_2859 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Core.RecordDef.params
d_params_112 ::
  T_RecordDef_100 -> [MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112]
d_params_112 v0
  = case coe v0 of
      C_RecordDef'46'constructor_2859 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Utils.Core.parameters
d_parameters_114 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Definition_280 -> Integer
d_parameters_114 v0
  = let v1 = 0 :: Integer in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'type_290 v2 v3
           -> coe v2
         _ -> coe v1)
-- Reflection.Utils.Core.toTelescope
d_toTelescope_118 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_toTelescope_118
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v1 v2
                -> coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Reflection.Utils.Core.fromTelescope
d_fromTelescope_126 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112]
d_fromTelescope_126
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
                -> coe
                     MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 (coe v1) (coe v2)
              _ -> MAlonzo.RTE.mazUnreachableError))
