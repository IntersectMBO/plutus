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

module MAlonzo.Code.Class.MonadTC where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Applicative.Core
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Class.DecEq.Instances
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Class.Functor.Instances
import qualified MAlonzo.Code.Class.Monad.Core
import qualified MAlonzo.Code.Class.MonadError
import qualified MAlonzo.Code.Class.MonadReader
import qualified MAlonzo.Code.Class.Show.Core
import qualified MAlonzo.Code.Class.Show.Instances
import qualified MAlonzo.Code.Class.Traversable.Core
import qualified MAlonzo.Code.Class.Traversable.Instances
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Reflection.Debug

-- Class.MonadTC.ReductionOptions
d_ReductionOptions_4 = ()
data T_ReductionOptions_4
  = C_onlyReduce_6 [AgdaAny] | C_dontReduce_8 [AgdaAny]
-- Class.MonadTC.reduceAll
d_reduceAll_10 :: T_ReductionOptions_4
d_reduceAll_10
  = coe
      C_dontReduce_8 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Class.MonadTC.TCOptions
d_TCOptions_12 = ()
data T_TCOptions_12
  = C_TCOptions'46'constructor_49 MAlonzo.Code.Reflection.Debug.T_DebugOptions_232
                                  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Class.MonadTC.TCOptions.debug
d_debug_18 ::
  T_TCOptions_12 -> MAlonzo.Code.Reflection.Debug.T_DebugOptions_232
d_debug_18 v0
  = case coe v0 of
      C_TCOptions'46'constructor_49 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.TCOptions.fuel
d_fuel_20 ::
  T_TCOptions_12 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_fuel_20 v0
  = case coe v0 of
      C_TCOptions'46'constructor_49 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.defaultTCOptions
d_defaultTCOptions_22 :: T_TCOptions_12
d_defaultTCOptions_22
  = coe
      C_TCOptions'46'constructor_49
      (coe MAlonzo.Code.Reflection.Debug.d_defaultDebugOptions_254)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Class.MonadTC.TCEnv
d_TCEnv_24 = ()
data T_TCEnv_24
  = C_TCEnv'46'constructor_205 Bool Bool Bool T_ReductionOptions_4
                               [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                               [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                               MAlonzo.Code.Data.Sum.Base.T__'8846'__30 T_TCOptions_12
-- Class.MonadTC.TCEnv.normalisation
d_normalisation_42 :: T_TCEnv_24 -> Bool
d_normalisation_42 v0
  = case coe v0 of
      C_TCEnv'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.TCEnv.reconstruction
d_reconstruction_44 :: T_TCEnv_24 -> Bool
d_reconstruction_44 v0
  = case coe v0 of
      C_TCEnv'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.TCEnv.noConstraints
d_noConstraints_46 :: T_TCEnv_24 -> Bool
d_noConstraints_46 v0
  = case coe v0 of
      C_TCEnv'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.TCEnv.reduction
d_reduction_48 :: T_TCEnv_24 -> T_ReductionOptions_4
d_reduction_48 v0
  = case coe v0 of
      C_TCEnv'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.TCEnv.globalContext
d_globalContext_50 ::
  T_TCEnv_24 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_globalContext_50 v0
  = case coe v0 of
      C_TCEnv'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.TCEnv.localContext
d_localContext_52 ::
  T_TCEnv_24 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_localContext_52 v0
  = case coe v0 of
      C_TCEnv'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.TCEnv.goal
d_goal_54 :: T_TCEnv_24 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_goal_54 v0
  = case coe v0 of
      C_TCEnv'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.TCEnv.options
d_options_56 :: T_TCEnv_24 -> T_TCOptions_12
d_options_56 v0
  = case coe v0 of
      C_TCEnv'46'constructor_205 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.TCEnv._.debug
d_debug_60 ::
  T_TCEnv_24 -> MAlonzo.Code.Reflection.Debug.T_DebugOptions_232
d_debug_60 v0 = coe d_debug_18 (coe d_options_56 (coe v0))
-- Class.MonadTC.TCEnv._.fuel
d_fuel_62 :: T_TCEnv_24 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_fuel_62 v0 = coe d_fuel_20 (coe d_options_56 (coe v0))
-- Class.MonadTC.initTCEnvWithGoal
d_initTCEnvWithGoal_64 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_initTCEnvWithGoal_64 v0
  = coe
      MAlonzo.Code.Class.Functor.Core.du__'60''38''62'__30
      (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'TC_436)
      (coe ()) (coe ())
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_getContext_376)
      (coe
         (\ v1 ->
            coe
              C_TCEnv'46'constructor_205
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe d_reduceAll_10)
              (coe v1) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v0))
              (coe d_defaultTCOptions_22)))
-- Class.MonadTC.initTCEnv
d_initTCEnv_70 :: AgdaAny
d_initTCEnv_70
  = coe
      d_initTCEnvWithGoal_64
      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216)
-- Class.MonadTC.MonadTC
d_MonadTC_80 a0 a1 a2 = ()
data T_MonadTC_80
  = C_MonadTC'46'constructor_5621 (MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
                                   MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny)
                                  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                   () ->
                                   [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] ->
                                   AgdaAny)
                                  (MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny)
                                  (MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
                                   MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny)
                                  (MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny)
                                  (MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny)
                                  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                   () -> AgdaAny -> AgdaAny)
                                  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                   () -> MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny)
                                  (() -> AgdaAny -> AgdaAny)
                                  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny)
                                  (MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
                                   MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny)
                                  (MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
                                   MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny)
                                  (AgdaAny ->
                                   [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny)
                                  (AgdaAny -> AgdaAny) (AgdaAny -> AgdaAny)
                                  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                   () -> AgdaAny -> AgdaAny)
                                  AgdaAny (AgdaAny -> AgdaAny)
                                  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                                   Integer ->
                                   [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] ->
                                   AgdaAny)
                                  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                   () -> AgdaAny -> AgdaAny)
                                  (AgdaAny -> AgdaAny)
-- Class.MonadTC.MonadTC.unify
d_unify_132 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_unify_132 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.typeError
d_typeError_134 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] -> AgdaAny
d_typeError_134 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.inferType
d_inferType_136 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_inferType_136 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.checkType
d_checkType_138 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_checkType_138 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.normalise
d_normalise_140 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_normalise_140 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.reduce
d_reduce_142 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_reduce_142 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.quoteTC
d_quoteTC_144 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_quoteTC_144 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.unquoteTC
d_unquoteTC_146 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_unquoteTC_146 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.quoteωTC
d_quoteωTC_150 :: T_MonadTC_80 -> () -> AgdaAny -> AgdaAny
d_quoteωTC_150 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.freshName
d_freshName_152 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_freshName_152 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.declareDef
d_declareDef_154 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_declareDef_154 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v11
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.declarePostulate
d_declarePostulate_156 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_declarePostulate_156 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.defineFun
d_defineFun_158 ::
  T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
d_defineFun_158 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v13
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.getType
d_getType_160 :: T_MonadTC_80 -> AgdaAny -> AgdaAny
d_getType_160 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v14
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.getDefinition
d_getDefinition_162 :: T_MonadTC_80 -> AgdaAny -> AgdaAny
d_getDefinition_162 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v15
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.blockOnMeta
d_blockOnMeta_164 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_blockOnMeta_164 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.commitTC
d_commitTC_166 :: T_MonadTC_80 -> AgdaAny
d_commitTC_166 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v17
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.isMacro
d_isMacro_168 :: T_MonadTC_80 -> AgdaAny -> AgdaAny
d_isMacro_168 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.debugPrint
d_debugPrint_170 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] -> AgdaAny
d_debugPrint_170 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v19
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.runSpeculative
d_runSpeculative_172 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_runSpeculative_172 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v20
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.getInstances
d_getInstances_174 :: T_MonadTC_80 -> AgdaAny -> AgdaAny
d_getInstances_174 v0
  = case coe v0 of
      C_MonadTC'46'constructor_5621 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21
        -> coe v21
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.runAndReset
d_runAndReset_182 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_runAndReset_182 ~v0 v1 ~v2 v3 v4 ~v5 v6
  = du_runAndReset_182 v1 v3 v4 v6
du_runAndReset_182 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny -> AgdaAny
du_runAndReset_182 v0 v1 v2 v3
  = coe
      d_runSpeculative_172 v1 v2 erased
      (coe
         MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
         (MAlonzo.Code.Class.Applicative.Core.d_super_18
            (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
         v2 erased v2 erased
         (\ v4 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8))
         v3)
-- Class.MonadTC.MonadTC.isSuccessful
d_isSuccessful_188 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_isSuccessful_188 ~v0 v1 v2 v3 v4 ~v5 v6
  = du_isSuccessful_188 v1 v2 v3 v4 v6
du_isSuccessful_188 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny -> AgdaAny
du_isSuccessful_188 v0 v1 v2 v3 v4
  = coe
      du_runAndReset_182 (coe v0) (coe v2) (coe ())
      (coe
         MAlonzo.Code.Class.MonadError.d_catch_28 v1 () erased
         (coe
            MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe v3)
            (coe ()) (coe v4)
            (coe
               MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
               (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)))
         (\ v5 ->
            coe
              MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
              (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)))
-- Class.MonadTC.MonadTC.isDef
d_isDef_194 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 -> AgdaAny -> AgdaAny
d_isDef_194 ~v0 v1 ~v2 v3 v4 = du_isDef_194 v1 v3 v4
du_isDef_194 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 -> AgdaAny -> AgdaAny
du_isDef_194 v0 v1 v2
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe d_getDefinition_162 v1 v2)
      (\ v3 ->
         let v4
               = coe
                   MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) in
         coe
           (case coe v3 of
              MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'cons_302 v5 v6
                -> coe
                     MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
              _ -> coe v4))
-- Class.MonadTC.MonadTC.isCon
d_isCon_200 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 -> AgdaAny -> AgdaAny
d_isCon_200 ~v0 v1 ~v2 v3 v4 = du_isCon_200 v1 v3 v4
du_isCon_200 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 -> AgdaAny -> AgdaAny
du_isCon_200 v0 v1 v2
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe d_getDefinition_162 v1 v2)
      (\ v3 ->
         let v4
               = coe
                   MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                   (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) in
         coe
           (case coe v3 of
              MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'cons_302 v5 v6
                -> coe
                     MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
              _ -> coe v4))
-- Class.MonadTC.MonadTC.nameConstr
d_nameConstr_206 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
d_nameConstr_206 ~v0 v1 v2 v3 v4 v5
  = du_nameConstr_206 v1 v2 v3 v4 v5
du_nameConstr_206 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
du_nameConstr_206 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe du_isDef_194 (coe v0) (coe v2) (coe v3))
      (\ v5 ->
         coe
           MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
           erased (coe du_isCon_200 (coe v0) (coe v2) (coe v3))
           (\ v6 ->
              if coe v5
                then coe
                       MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                       (coe
                          MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 (coe v3) (coe v4))
                else (if coe v6
                        then coe
                               MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 (coe v3) (coe v4))
                        else coe
                               MAlonzo.Code.Class.MonadError.d_error_26 v1 () erased
                               (coe
                                  MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12 v3)
                                     (coe
                                        ("is neither a definition nor a constructor!"
                                         ::
                                         Data.Text.Text)))
                                  (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Class.MonadTC.MonadTC.termFromName
d_termFromName_218 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 -> AgdaAny -> AgdaAny
d_termFromName_218 ~v0 v1 v2 v3 v4
  = du_termFromName_218 v1 v2 v3 v4
du_termFromName_218 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 -> AgdaAny -> AgdaAny
du_termFromName_218 v0 v1 v2 v3
  = coe
      du_nameConstr_206 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Class.MonadTC.MonadTC.mkRecord
d_mkRecord_222 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
d_mkRecord_222 ~v0 v1 v2 v3 v4 v5 = du_mkRecord_222 v1 v2 v3 v4 v5
du_mkRecord_222 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
du_mkRecord_222 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe d_getDefinition_162 v2 v3)
      (\ v5 ->
         let v6
               = coe
                   MAlonzo.Code.Class.MonadError.d_error_26 v1 () erased
                   (coe
                      MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                      (coe ("Not a record!" :: Data.Text.Text))
                      (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)) in
         coe
           (case coe v5 of
              MAlonzo.Code.Agda.Builtin.Reflection.C_record'45'type_296 v7 v8
                -> coe
                     MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                     (coe
                        MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 (coe v7) (coe v4))
              _ -> coe v6))
-- Class.MonadTC.MonadTC.isSolvedMeta
d_isSolvedMeta_232 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_isSolvedMeta_232 ~v0 v1 v2 v3 v4
  = du_isSolvedMeta_232 v1 v2 v3 v4
du_isSolvedMeta_232 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_isSolvedMeta_232 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Class.MonadError.d_error_26 v1 () erased
              (coe
                 MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                 (coe ("Not a meta!" :: Data.Text.Text))
                 (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v5 v6
           -> coe
                MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                erased (coe d_reduce_142 v2 v3)
                (\ v7 ->
                   let v8
                         = coe
                             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10) in
                   coe
                     (case coe v7 of
                        MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v9 v10
                          -> coe
                               MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                               (coe
                                  MAlonzo.Code.Class.DecEq.Core.du__'8800'__26 (coe ())
                                  (coe MAlonzo.Code.Class.DecEq.Instances.d_DecEq'45'Meta_212)
                                  (coe v5) (coe v9))
                        _ -> coe v8))
         _ -> coe v4)
-- Class.MonadTC.MonadTC.hasUnsolvedMetas
d_hasUnsolvedMetas_246 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_hasUnsolvedMetas_246 ~v0 v1 v2 v3 v4
  = du_hasUnsolvedMetas_246 v1 v2 v3 v4
du_hasUnsolvedMetas_246 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_hasUnsolvedMetas_246 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_var_172 v4 v5
        -> coe
             du_hasUnsolvedMetas''_248 (coe v0) (coe v1) (coe v2) (coe v5)
      MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 v4 v5
        -> coe
             du_hasUnsolvedMetas''_248 (coe v0) (coe v1) (coe v2) (coe v5)
      MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 v4 v5
        -> coe
             du_hasUnsolvedMetas''_248 (coe v0) (coe v1) (coe v2) (coe v5)
      MAlonzo.Code.Agda.Builtin.Reflection.C_lam_190 v4 v5
        -> case coe v5 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v6 v7
               -> coe du_hasUnsolvedMetas_246 (coe v0) (coe v1) (coe v2) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196 v4 v5
        -> coe
             MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
             erased
             (coe du_hasUnsolvedMetasCl_250 (coe v0) (coe v1) (coe v2) (coe v4))
             (\ v6 ->
                coe
                  MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                  erased
                  (coe du_hasUnsolvedMetas''_248 (coe v0) (coe v1) (coe v2) (coe v5))
                  (\ v7 ->
                     coe
                       MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                       (MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v6) (coe v7))))
      MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202 v4 v5
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v6 v7
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v8 v9
                      -> coe
                           MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                           erased
                           (coe du_hasUnsolvedMetas_246 (coe v0) (coe v1) (coe v2) (coe v7))
                           (\ v10 ->
                              coe
                                MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                                erased
                                (coe du_hasUnsolvedMetas_246 (coe v0) (coe v1) (coe v2) (coe v9))
                                (\ v11 ->
                                   coe
                                     MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                                     (MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                        (coe v10) (coe v11))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Reflection.C_agda'45'sort_206 v4
        -> let v5
                 = coe
                     MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                     (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Reflection.C_set_220 v6
                  -> coe du_hasUnsolvedMetas_246 (coe v0) (coe v1) (coe v2) (coe v6)
                MAlonzo.Code.Agda.Builtin.Reflection.C_prop_228 v6
                  -> coe du_hasUnsolvedMetas_246 (coe v0) (coe v1) (coe v2) (coe v6)
                MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_238
                  -> coe
                       MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                       (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                _ -> coe v5)
      MAlonzo.Code.Agda.Builtin.Reflection.C_lit_210 v4
        -> coe
             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v4 v5
        -> coe
             MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
             (MAlonzo.Code.Class.Applicative.Core.d_super_18
                (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
             () erased () erased MAlonzo.Code.Data.Bool.Base.d_not_22
             (coe du_isSolvedMeta_232 (coe v0) (coe v1) (coe v2) (coe v3))
      MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216
        -> coe
             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.hasUnsolvedMetas'
d_hasUnsolvedMetas''_248 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
d_hasUnsolvedMetas''_248 ~v0 v1 v2 v3 v4
  = du_hasUnsolvedMetas''_248 v1 v2 v3 v4
du_hasUnsolvedMetas''_248 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
du_hasUnsolvedMetas''_248 v0 v1 v2 v3
  = case coe v3 of
      []
        -> coe
             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v6 v7
               -> coe
                    MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                    erased
                    (coe du_hasUnsolvedMetas_246 (coe v0) (coe v1) (coe v2) (coe v7))
                    (\ v8 ->
                       coe
                         MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                         erased
                         (coe du_hasUnsolvedMetas''_248 (coe v0) (coe v1) (coe v2) (coe v5))
                         (\ v9 ->
                            coe
                              MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                              (MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v8) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.hasUnsolvedMetasCl
d_hasUnsolvedMetasCl_250 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
d_hasUnsolvedMetasCl_250 ~v0 v1 v2 v3 v4
  = du_hasUnsolvedMetasCl_250 v1 v2 v3 v4
du_hasUnsolvedMetasCl_250 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
du_hasUnsolvedMetasCl_250 v0 v1 v2 v3
  = case coe v3 of
      []
        -> coe
             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272 v6 v7 v8
               -> coe
                    MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                    erased
                    (coe du_hasUnsolvedMetas_246 (coe v0) (coe v1) (coe v2) (coe v8))
                    (\ v9 ->
                       coe
                         MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                         erased
                         (coe
                            du_hasUnsolvedMetasTel_252 (coe v0) (coe v1) (coe v2) (coe v6))
                         (\ v10 ->
                            coe
                              MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                              erased
                              (coe du_hasUnsolvedMetasCl_250 (coe v0) (coe v1) (coe v2) (coe v5))
                              (\ v11 ->
                                 coe
                                   MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                                   (MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                      (coe v9)
                                      (coe
                                         MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v10)
                                         (coe v11))))))
             MAlonzo.Code.Agda.Builtin.Reflection.C_absurd'45'clause_278 v6 v7
               -> coe
                    MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                    erased
                    (coe
                       du_hasUnsolvedMetasTel_252 (coe v0) (coe v1) (coe v2) (coe v6))
                    (\ v8 ->
                       coe
                         MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                         erased
                         (coe du_hasUnsolvedMetasCl_250 (coe v0) (coe v1) (coe v2) (coe v5))
                         (\ v9 ->
                            coe
                              MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                              (MAlonzo.Code.Data.Bool.Base.d__'8744'__30 (coe v8) (coe v9))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.hasUnsolvedMetasTel
d_hasUnsolvedMetasTel_252 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_hasUnsolvedMetasTel_252 ~v0 v1 v2 v3 v4
  = du_hasUnsolvedMetasTel_252 v1 v2 v3 v4
du_hasUnsolvedMetasTel_252 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_hasUnsolvedMetasTel_252 v0 v1 v2 v3
  = case coe v3 of
      []
        -> coe
             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (:) v4 v5
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v8 v9
                      -> coe
                           MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                           erased
                           (coe du_hasUnsolvedMetas_246 (coe v0) (coe v1) (coe v2) (coe v9))
                           (\ v10 ->
                              coe
                                MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                                erased
                                (coe
                                   du_hasUnsolvedMetasTel_252 (coe v0) (coe v1) (coe v2) (coe v5))
                                (\ v11 ->
                                   coe
                                     MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                                     (MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                                        (coe v10) (coe v11))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC.MonadTC.declareAndDefineFuns
d_declareAndDefineFuns_334 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_declareAndDefineFuns_334 ~v0 v1 ~v2 v3 v4
  = du_declareAndDefineFuns_334 v1 v3 v4
du_declareAndDefineFuns_334 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_declareAndDefineFuns_334 v0 v1 v2
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
      (coe ())
      (coe
         MAlonzo.Code.Class.Traversable.Core.du_traverse_44
         (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
         (coe
            MAlonzo.Code.Class.Traversable.Instances.d_TraversableM'45'List_28)
         (coe ()) (coe ()) (coe v0)
         (coe
            (\ v3 ->
               coe
                 d_declareDef_154 v1
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))))
         (coe v2))
      (coe
         MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
         (coe ())
         (coe
            MAlonzo.Code.Class.Traversable.Core.du_traverse_44
            (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
            (coe
               MAlonzo.Code.Class.Traversable.Instances.d_TraversableM'45'List_28)
            (coe ()) (coe ()) (coe v0)
            (coe
               (\ v3 ->
                  case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> case coe v4 of
                           MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v6 v7
                             -> case coe v5 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                                    -> coe d_defineFun_158 v1 v7 v9
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError))
            (coe v2))
         (coe
            MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Class.MonadTC.MonadTC.declareAndDefineFunsDebug
d_declareAndDefineFunsDebug_350 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_declareAndDefineFunsDebug_350 ~v0 v1 v2 v3 v4
  = du_declareAndDefineFunsDebug_350 v1 v2 v3 v4
du_declareAndDefineFunsDebug_350 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_declareAndDefineFunsDebug_350 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
      (coe ())
      (coe
         MAlonzo.Code.Class.Traversable.Core.du_traverse_44
         (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
         (coe
            MAlonzo.Code.Class.Traversable.Instances.d_TraversableM'45'List_28)
         (coe ()) (coe ()) (coe v0)
         (coe
            (\ v4 ->
               coe
                 d_declareDef_154 v2
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))))
         (coe v3))
      (coe
         MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
         (coe ())
         (coe
            MAlonzo.Code.Class.Traversable.Core.du_traverse_44
            (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
            (coe
               MAlonzo.Code.Class.Traversable.Instances.d_TraversableM'45'List_28)
            (coe ()) (coe ()) (coe v0)
            (coe
               (\ v4 ->
                  case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v7 v8
                             -> coe
                                  seq (coe v6)
                                  (coe
                                     MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased
                                     () erased
                                     (coe
                                        MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 ()
                                        erased () erased (coe d_getType_160 v2 v8)
                                        (coe du_hasUnsolvedMetas_246 (coe v0) (coe v1) (coe v2)))
                                     (\ v9 ->
                                        coe
                                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v9)
                                          (coe
                                             MAlonzo.Code.Class.MonadError.d_error_26 v1 () erased
                                             (coe
                                                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_strErr_310
                                                   (coe
                                                      MAlonzo.Code.Class.Show.Core.d_show_16
                                                      MAlonzo.Code.Class.Show.Instances.d_Show'45'Name_68
                                                      v8))))
                                          (coe
                                             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError))
            (coe v3))
         (coe
            MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
            (coe ())
            (coe
               MAlonzo.Code.Class.Traversable.Core.du_traverse_44
               (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
               (coe
                  MAlonzo.Code.Class.Traversable.Instances.d_TraversableM'45'List_28)
               (coe ()) (coe ()) (coe v0)
               (coe
                  (\ v4 ->
                     case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> case coe v5 of
                              MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v7 v8
                                -> case coe v6 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                       -> coe d_defineFun_158 v2 v8 v10
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError))
               (coe v3))
            (coe
               MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
               (coe ())
               (coe
                  MAlonzo.Code.Class.Traversable.Core.du_traverse_44
                  (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
                  (coe
                     MAlonzo.Code.Class.Traversable.Instances.d_TraversableM'45'List_28)
                  (coe ()) (coe ()) (coe v0)
                  (coe
                     (\ v4 ->
                        case coe v4 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                            -> case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v7 v8
                                   -> coe
                                        seq (coe v6)
                                        (coe
                                           MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 ()
                                           erased () erased (coe d_getDefinition_162 v2 v8)
                                           (\ v9 ->
                                              let v10
                                                    = coe
                                                        MAlonzo.Code.Class.MonadError.d_error_26 v1
                                                        () erased
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_strErr_310
                                                              (coe
                                                                 ("Weird bug"
                                                                  ::
                                                                  Data.Text.Text)))) in
                                              coe
                                                (case coe v9 of
                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_function_284 v11
                                                     -> coe
                                                          MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22
                                                          v0 () erased () erased
                                                          (coe
                                                             du_hasUnsolvedMetasCl_250 (coe v0)
                                                             (coe v1) (coe v2) (coe v11))
                                                          (\ v12 ->
                                                             coe
                                                               MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                                               (coe v12)
                                                               (coe
                                                                  MAlonzo.Code.Class.MonadError.d_error_26
                                                                  v1 () erased
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_strErr_310
                                                                        (coe
                                                                           MAlonzo.Code.Class.Show.Core.d_show_16
                                                                           MAlonzo.Code.Class.Show.Instances.d_Show'45'Definition_106
                                                                           v9))))
                                                               (coe
                                                                  MAlonzo.Code.Class.Monad.Core.d_return_20
                                                                  v0 () erased
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                                   _ -> coe v10)))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
                  (coe v3))
               (coe
                  MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))))
-- Class.MonadTC.MonadTC.declareAndDefineFun
d_declareAndDefineFun_384 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
d_declareAndDefineFun_384 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_declareAndDefineFun_384 v1 v3 v4 v5 v6
du_declareAndDefineFun_384 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
du_declareAndDefineFun_384 v0 v1 v2 v3 v4
  = coe
      du_declareAndDefineFuns_334 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))))
-- Class.MonadTC.MonadTC.newMeta
d_newMeta_392 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_newMeta_392 ~v0 ~v1 ~v2 v3 = du_newMeta_392 v3
du_newMeta_392 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_newMeta_392 v0
  = coe
      d_checkType_138 v0
      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216)
-- Class.MonadTC._._.blockOnMeta
d_blockOnMeta_418 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_blockOnMeta_418 ~v0 ~v1 ~v2 v3 ~v4 = du_blockOnMeta_418 v3
du_blockOnMeta_418 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
du_blockOnMeta_418 v0 = coe d_blockOnMeta_164 (coe v0)
-- Class.MonadTC._._.checkType
d_checkType_420 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_checkType_420 ~v0 ~v1 ~v2 v3 ~v4 = du_checkType_420 v3
du_checkType_420 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_checkType_420 v0 = coe d_checkType_138 (coe v0)
-- Class.MonadTC._._.commitTC
d_commitTC_422 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 -> AgdaAny
d_commitTC_422 ~v0 ~v1 ~v2 v3 ~v4 = du_commitTC_422 v3
du_commitTC_422 :: T_MonadTC_80 -> AgdaAny
du_commitTC_422 v0 = coe d_commitTC_166 (coe v0)
-- Class.MonadTC._._.debugPrint
d_debugPrint_424 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] -> AgdaAny
d_debugPrint_424 ~v0 ~v1 ~v2 v3 ~v4 = du_debugPrint_424 v3
du_debugPrint_424 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] -> AgdaAny
du_debugPrint_424 v0 = coe d_debugPrint_170 (coe v0)
-- Class.MonadTC._._.declareAndDefineFun
d_declareAndDefineFun_426 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
d_declareAndDefineFun_426 ~v0 v1 ~v2 v3 ~v4
  = du_declareAndDefineFun_426 v1 v3
du_declareAndDefineFun_426 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
du_declareAndDefineFun_426 v0 v1
  = coe du_declareAndDefineFun_384 (coe v0) (coe v1)
-- Class.MonadTC._._.declareAndDefineFuns
d_declareAndDefineFuns_428 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_declareAndDefineFuns_428 ~v0 v1 ~v2 v3 ~v4
  = du_declareAndDefineFuns_428 v1 v3
du_declareAndDefineFuns_428 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_declareAndDefineFuns_428 v0 v1
  = coe du_declareAndDefineFuns_334 (coe v0) (coe v1)
-- Class.MonadTC._._.declareAndDefineFunsDebug
d_declareAndDefineFunsDebug_430 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_declareAndDefineFunsDebug_430 ~v0 v1 v2 v3 ~v4
  = du_declareAndDefineFunsDebug_430 v1 v2 v3
du_declareAndDefineFunsDebug_430 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_declareAndDefineFunsDebug_430 v0 v1 v2
  = coe du_declareAndDefineFunsDebug_350 (coe v0) (coe v1) (coe v2)
-- Class.MonadTC._._.declareDef
d_declareDef_432 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_declareDef_432 ~v0 ~v1 ~v2 v3 ~v4 = du_declareDef_432 v3
du_declareDef_432 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_declareDef_432 v0 = coe d_declareDef_154 (coe v0)
-- Class.MonadTC._._.declarePostulate
d_declarePostulate_434 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_declarePostulate_434 ~v0 ~v1 ~v2 v3 ~v4
  = du_declarePostulate_434 v3
du_declarePostulate_434 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_declarePostulate_434 v0 = coe d_declarePostulate_156 (coe v0)
-- Class.MonadTC._._.defineFun
d_defineFun_436 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
d_defineFun_436 ~v0 ~v1 ~v2 v3 ~v4 = du_defineFun_436 v3
du_defineFun_436 ::
  T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
du_defineFun_436 v0 = coe d_defineFun_158 (coe v0)
-- Class.MonadTC._._.freshName
d_freshName_438 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_freshName_438 ~v0 ~v1 ~v2 v3 ~v4 = du_freshName_438 v3
du_freshName_438 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
du_freshName_438 v0 = coe d_freshName_152 (coe v0)
-- Class.MonadTC._._.getDefinition
d_getDefinition_440 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny -> AgdaAny
d_getDefinition_440 ~v0 ~v1 ~v2 v3 ~v4 = du_getDefinition_440 v3
du_getDefinition_440 :: T_MonadTC_80 -> AgdaAny -> AgdaAny
du_getDefinition_440 v0 = coe d_getDefinition_162 (coe v0)
-- Class.MonadTC._._.getInstances
d_getInstances_442 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny -> AgdaAny
d_getInstances_442 ~v0 ~v1 ~v2 v3 ~v4 = du_getInstances_442 v3
du_getInstances_442 :: T_MonadTC_80 -> AgdaAny -> AgdaAny
du_getInstances_442 v0 = coe d_getInstances_174 (coe v0)
-- Class.MonadTC._._.getType
d_getType_444 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny -> AgdaAny
d_getType_444 ~v0 ~v1 ~v2 v3 ~v4 = du_getType_444 v3
du_getType_444 :: T_MonadTC_80 -> AgdaAny -> AgdaAny
du_getType_444 v0 = coe d_getType_160 (coe v0)
-- Class.MonadTC._._.hasUnsolvedMetas
d_hasUnsolvedMetas_446 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_hasUnsolvedMetas_446 ~v0 v1 v2 v3 ~v4
  = du_hasUnsolvedMetas_446 v1 v2 v3
du_hasUnsolvedMetas_446 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_hasUnsolvedMetas_446 v0 v1 v2
  = coe du_hasUnsolvedMetas_246 (coe v0) (coe v1) (coe v2)
-- Class.MonadTC._._.hasUnsolvedMetas'
d_hasUnsolvedMetas''_448 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
d_hasUnsolvedMetas''_448 ~v0 v1 v2 v3 ~v4
  = du_hasUnsolvedMetas''_448 v1 v2 v3
du_hasUnsolvedMetas''_448 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
du_hasUnsolvedMetas''_448 v0 v1 v2
  = coe du_hasUnsolvedMetas''_248 (coe v0) (coe v1) (coe v2)
-- Class.MonadTC._._.hasUnsolvedMetasCl
d_hasUnsolvedMetasCl_450 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
d_hasUnsolvedMetasCl_450 ~v0 v1 v2 v3 ~v4
  = du_hasUnsolvedMetasCl_450 v1 v2 v3
du_hasUnsolvedMetasCl_450 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
du_hasUnsolvedMetasCl_450 v0 v1 v2
  = coe du_hasUnsolvedMetasCl_250 (coe v0) (coe v1) (coe v2)
-- Class.MonadTC._._.hasUnsolvedMetasTel
d_hasUnsolvedMetasTel_452 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_hasUnsolvedMetasTel_452 ~v0 v1 v2 v3 ~v4
  = du_hasUnsolvedMetasTel_452 v1 v2 v3
du_hasUnsolvedMetasTel_452 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_hasUnsolvedMetasTel_452 v0 v1 v2
  = coe du_hasUnsolvedMetasTel_252 (coe v0) (coe v1) (coe v2)
-- Class.MonadTC._._.inferType
d_inferType_454 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_inferType_454 ~v0 ~v1 ~v2 v3 ~v4 = du_inferType_454 v3
du_inferType_454 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_inferType_454 v0 = coe d_inferType_136 (coe v0)
-- Class.MonadTC._._.isCon
d_isCon_456 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny -> AgdaAny
d_isCon_456 ~v0 v1 ~v2 v3 ~v4 = du_isCon_456 v1 v3
du_isCon_456 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 -> AgdaAny -> AgdaAny
du_isCon_456 v0 v1 = coe du_isCon_200 (coe v0) (coe v1)
-- Class.MonadTC._._.isDef
d_isDef_458 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny -> AgdaAny
d_isDef_458 ~v0 v1 ~v2 v3 ~v4 = du_isDef_458 v1 v3
du_isDef_458 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 -> AgdaAny -> AgdaAny
du_isDef_458 v0 v1 = coe du_isDef_194 (coe v0) (coe v1)
-- Class.MonadTC._._.isMacro
d_isMacro_460 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny -> AgdaAny
d_isMacro_460 ~v0 ~v1 ~v2 v3 ~v4 = du_isMacro_460 v3
du_isMacro_460 :: T_MonadTC_80 -> AgdaAny -> AgdaAny
du_isMacro_460 v0 = coe d_isMacro_168 (coe v0)
-- Class.MonadTC._._.isSolvedMeta
d_isSolvedMeta_462 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_isSolvedMeta_462 ~v0 v1 v2 v3 ~v4 = du_isSolvedMeta_462 v1 v2 v3
du_isSolvedMeta_462 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_isSolvedMeta_462 v0 v1 v2
  = coe du_isSolvedMeta_232 (coe v0) (coe v1) (coe v2)
-- Class.MonadTC._._.isSuccessful
d_isSuccessful_464 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_isSuccessful_464 ~v0 v1 v2 v3 ~v4 = du_isSuccessful_464 v1 v2 v3
du_isSuccessful_464 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
du_isSuccessful_464 v0 v1 v2 v3 v4 v5
  = coe du_isSuccessful_188 (coe v0) (coe v1) (coe v2) v3 v5
-- Class.MonadTC._._.mkRecord
d_mkRecord_466 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
d_mkRecord_466 ~v0 v1 v2 v3 ~v4 = du_mkRecord_466 v1 v2 v3
du_mkRecord_466 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
du_mkRecord_466 v0 v1 v2
  = coe du_mkRecord_222 (coe v0) (coe v1) (coe v2)
-- Class.MonadTC._._.nameConstr
d_nameConstr_468 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
d_nameConstr_468 ~v0 v1 v2 v3 ~v4 = du_nameConstr_468 v1 v2 v3
du_nameConstr_468 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
du_nameConstr_468 v0 v1 v2
  = coe du_nameConstr_206 (coe v0) (coe v1) (coe v2)
-- Class.MonadTC._._.newMeta
d_newMeta_470 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_newMeta_470 ~v0 ~v1 ~v2 v3 ~v4 = du_newMeta_470 v3
du_newMeta_470 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_newMeta_470 v0 = coe du_newMeta_392 (coe v0)
-- Class.MonadTC._._.normalise
d_normalise_472 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_normalise_472 ~v0 ~v1 ~v2 v3 ~v4 = du_normalise_472 v3
du_normalise_472 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_normalise_472 v0 = coe d_normalise_140 (coe v0)
-- Class.MonadTC._._.quoteTC
d_quoteTC_474 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_quoteTC_474 ~v0 ~v1 ~v2 v3 ~v4 = du_quoteTC_474 v3
du_quoteTC_474 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
du_quoteTC_474 v0 = coe d_quoteTC_144 (coe v0)
-- Class.MonadTC._._.quoteωTC
d_quoteωTC_476 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  () -> AgdaAny -> AgdaAny
d_quoteωTC_476 ~v0 ~v1 ~v2 v3 ~v4 = du_quoteωTC_476 v3
du_quoteωTC_476 :: T_MonadTC_80 -> () -> AgdaAny -> AgdaAny
du_quoteωTC_476 v0 = coe d_quoteωTC_150 (coe v0)
-- Class.MonadTC._._.reduce
d_reduce_478 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_reduce_478 ~v0 ~v1 ~v2 v3 ~v4 = du_reduce_478 v3
du_reduce_478 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_reduce_478 v0 = coe d_reduce_142 (coe v0)
-- Class.MonadTC._._.runAndReset
d_runAndReset_480 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_runAndReset_480 ~v0 v1 ~v2 v3 ~v4 = du_runAndReset_480 v1 v3
du_runAndReset_480 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
du_runAndReset_480 v0 v1 v2 v3 v4
  = coe du_runAndReset_182 (coe v0) (coe v1) v2 v4
-- Class.MonadTC._._.runSpeculative
d_runSpeculative_482 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_runSpeculative_482 ~v0 ~v1 ~v2 v3 ~v4 = du_runSpeculative_482 v3
du_runSpeculative_482 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
du_runSpeculative_482 v0 = coe d_runSpeculative_172 (coe v0)
-- Class.MonadTC._._.termFromName
d_termFromName_484 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny -> AgdaAny
d_termFromName_484 ~v0 v1 v2 v3 ~v4 = du_termFromName_484 v1 v2 v3
du_termFromName_484 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 -> AgdaAny -> AgdaAny
du_termFromName_484 v0 v1 v2
  = coe du_termFromName_218 (coe v0) (coe v1) (coe v2)
-- Class.MonadTC._._.typeError
d_typeError_486 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] -> AgdaAny
d_typeError_486 ~v0 ~v1 ~v2 v3 ~v4 = du_typeError_486 v3
du_typeError_486 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] -> AgdaAny
du_typeError_486 v0 = coe d_typeError_134 (coe v0)
-- Class.MonadTC._._.unify
d_unify_488 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_unify_488 ~v0 ~v1 ~v2 v3 ~v4 = du_unify_488 v3
du_unify_488 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_unify_488 v0 = coe d_unify_132 (coe v0)
-- Class.MonadTC._._.unquoteTC
d_unquoteTC_490 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_unquoteTC_490 ~v0 ~v1 ~v2 v3 ~v4 = du_unquoteTC_490 v3
du_unquoteTC_490 ::
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_unquoteTC_490 v0 = coe d_unquoteTC_146 (coe v0)
-- Class.MonadTC._.IsMErrorPart
d_IsMErrorPart_504 a0 a1 a2 a3 a4 a5 a6 = ()
newtype T_IsMErrorPart_504
  = C_IsMErrorPart'46'constructor_71671 (AgdaAny -> AgdaAny)
-- Class.MonadTC._.IsMErrorPart.toMErrorPart
d_toMErrorPart_510 :: T_IsMErrorPart_504 -> AgdaAny -> AgdaAny
d_toMErrorPart_510 v0
  = case coe v0 of
      C_IsMErrorPart'46'constructor_71671 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC._._.toMErrorPart
d_toMErrorPart_514 :: T_IsMErrorPart_504 -> AgdaAny -> AgdaAny
d_toMErrorPart_514 v0 = coe d_toMErrorPart_510 (coe v0)
-- Class.MonadTC._.MErrorPartWrap
d_MErrorPartWrap_516 a0 a1 a2 a3 a4 = ()
newtype T_MErrorPartWrap_516 = C_wrap_518 AgdaAny
-- Class.MonadTC._.IsMErrorPart-IsErrorPart
d_IsMErrorPart'45'IsErrorPart_522 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  () ->
  MAlonzo.Code.Reflection.Debug.T_IsErrorPart_6 -> T_IsMErrorPart_504
d_IsMErrorPart'45'IsErrorPart_522 ~v0 v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_IsMErrorPart'45'IsErrorPart_522 v1 v6
du_IsMErrorPart'45'IsErrorPart_522 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Reflection.Debug.T_IsErrorPart_6 -> T_IsMErrorPart_504
du_IsMErrorPart'45'IsErrorPart_522 v0 v1
  = coe
      C_IsMErrorPart'46'constructor_71671
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
              (coe
                 MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                 (coe MAlonzo.Code.Reflection.Debug.d_toErrorPart_12 v1 v2))))
-- Class.MonadTC._.IsMErrorPart-String
d_IsMErrorPart'45'String_526 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  T_IsMErrorPart_504
d_IsMErrorPart'45'String_526 ~v0 v1 ~v2 ~v3 ~v4
  = du_IsMErrorPart'45'String_526 v1
du_IsMErrorPart'45'String_526 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 -> T_IsMErrorPart_504
du_IsMErrorPart'45'String_526 v0
  = coe
      du_IsMErrorPart'45'IsErrorPart_522 (coe v0)
      (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
-- Class.MonadTC._.IsMErrorPart-Term
d_IsMErrorPart'45'Term_528 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  T_IsMErrorPart_504
d_IsMErrorPart'45'Term_528 ~v0 v1 ~v2 ~v3 ~v4
  = du_IsMErrorPart'45'Term_528 v1
du_IsMErrorPart'45'Term_528 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 -> T_IsMErrorPart_504
du_IsMErrorPart'45'Term_528 v0
  = coe
      du_IsMErrorPart'45'IsErrorPart_522 (coe v0)
      (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
-- Class.MonadTC._.IsMErrorPart-Name
d_IsMErrorPart'45'Name_530 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  T_IsMErrorPart_504
d_IsMErrorPart'45'Name_530 ~v0 v1 ~v2 ~v3 ~v4
  = du_IsMErrorPart'45'Name_530 v1
du_IsMErrorPart'45'Name_530 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 -> T_IsMErrorPart_504
du_IsMErrorPart'45'Name_530 v0
  = coe
      du_IsMErrorPart'45'IsErrorPart_522 (coe v0)
      (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Name_22)
-- Class.MonadTC._.IsMErrorPart-MErrorPartWrap
d_IsMErrorPart'45'MErrorPartWrap_532 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  T_IsMErrorPart_504
d_IsMErrorPart'45'MErrorPartWrap_532 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_IsMErrorPart'45'MErrorPartWrap_532
du_IsMErrorPart'45'MErrorPartWrap_532 :: T_IsMErrorPart_504
du_IsMErrorPart'45'MErrorPartWrap_532
  = coe
      C_IsMErrorPart'46'constructor_71671
      (coe
         (\ v0 ->
            case coe v0 of
              C_wrap_518 v1 -> coe v1
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.MonadTC._.[]ᵐ
d_'91''93''7504'_536 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 -> AgdaAny
d_'91''93''7504'_536 v0 ~v1 ~v2 ~v3 = du_'91''93''7504'_536 v0
du_'91''93''7504'_536 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 -> AgdaAny
du_'91''93''7504'_536 v0
  = coe
      MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Class.MonadTC._._∷ᵈᵐ_
d__'8759''7496''7504'__540 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> T_IsMErrorPart_504 -> AgdaAny -> AgdaAny
d__'8759''7496''7504'__540 ~v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du__'8759''7496''7504'__540 v1 v7 v8 v9
du__'8759''7496''7504'__540 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  AgdaAny -> T_IsMErrorPart_504 -> AgdaAny -> AgdaAny
du__'8759''7496''7504'__540 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe d_toMErrorPart_510 v2 v1)
      (\ v4 ->
         coe
           MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
           erased v3
           (\ v5 ->
              coe
                MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4) (coe v5))))
-- Class.MonadTC._._ᵛ
d__'7515'_550 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> T_MErrorPartWrap_516
d__'7515'_550 ~v0 v1 ~v2 v3 ~v4 v5 ~v6 v7
  = du__'7515'_550 v1 v3 v5 v7
du__'7515'_550 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> T_MErrorPartWrap_516
du__'7515'_550 v0 v1 v2 v3
  = coe
      C_wrap_518
      (coe
         MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
         erased (coe d_quoteTC_144 v1 v2 erased v3)
         (\ v4 ->
            coe
              MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
              (coe
                 MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v4)
                 (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Class.MonadTC._._ᵛⁿ
d__'7515''8319'_556 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> T_MErrorPartWrap_516
d__'7515''8319'_556 ~v0 v1 ~v2 v3 v4 v5 ~v6 v7
  = du__'7515''8319'_556 v1 v3 v4 v5 v7
du__'7515''8319'_556 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> T_MErrorPartWrap_516
du__'7515''8319'_556 v0 v1 v2 v3 v4
  = coe
      C_wrap_518
      (coe
         MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
         erased
         (coe
            MAlonzo.Code.Class.MonadReader.d_local_40 v2 () erased
            (\ v5 ->
               coe
                 C_TCEnv'46'constructor_205
                 (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                 (coe d_reconstruction_44 (coe v5))
                 (coe d_noConstraints_46 (coe v5)) (coe d_reduction_48 (coe v5))
                 (coe d_globalContext_50 (coe v5)) (coe d_localContext_52 (coe v5))
                 (coe d_goal_54 (coe v5)) (coe d_options_56 (coe v5)))
            (coe d_quoteTC_144 v1 v3 erased v4))
         (\ v5 ->
            coe
              MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
              (coe
                 MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v5)
                 (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Class.MonadTC._._ᵗ
d__'7511'_564 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  T_MErrorPartWrap_516
d__'7511'_564 v0 ~v1 v2 ~v3 v4 = du__'7511'_564 v0 v2 v4
du__'7511'_564 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  T_MErrorPartWrap_516
du__'7511'_564 v0 v1 v2
  = coe
      C_wrap_518
      (coe
         MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
         erased (coe d_inferType_136 v1 v2)
         (\ v3 ->
            coe
              MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
              (coe
                 MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v2)
                 (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                 (coe
                    MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                    (coe (" : " :: Data.Text.Text))
                    (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                    (coe
                       MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v3)
                       (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
-- Class.MonadTC._.debugLog
d_debugLog_570 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] -> AgdaAny
d_debugLog_570 ~v0 v1 ~v2 v3 v4 v5 = du_debugLog_570 v1 v3 v4 v5
du_debugLog_570 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] -> AgdaAny
du_debugLog_570 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (MAlonzo.Code.Class.MonadReader.d_ask_34 (coe v2))
      (\ v4 ->
         case coe v4 of
           C_TCEnv'46'constructor_205 v5 v6 v7 v8 v9 v10 v11 v12
             -> case coe v12 of
                  C_TCOptions'46'constructor_49 v13 v14
                    -> coe
                         MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                         (coe
                            MAlonzo.Code.Reflection.Debug.d_filter_248 v13
                            (MAlonzo.Code.Reflection.Debug.d_path_244 (coe v13)))
                         (coe
                            d_debugPrint_170 v1
                            (MAlonzo.Code.Reflection.Debug.d_debugOptionsPath_264 (coe v13))
                            (MAlonzo.Code.Reflection.Debug.d_level_250 (coe v13))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                               (coe
                                  MAlonzo.Code.Reflection.Debug.d_debugPrintPrefix_286 (coe v13))
                               (coe v3)))
                         (coe
                            MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                  _ -> MAlonzo.RTE.mazUnreachableError
           _ -> MAlonzo.RTE.mazUnreachableError)
-- Class.MonadTC._.debugLogᵐ
d_debugLog'7504'_578 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny -> AgdaAny
d_debugLog'7504'_578 ~v0 v1 ~v2 v3 v4 v5
  = du_debugLog'7504'_578 v1 v3 v4 v5
du_debugLog'7504'_578 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny -> AgdaAny
du_debugLog'7504'_578 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased v3 (coe du_debugLog_570 (coe v0) (coe v1) (coe v2))
-- Class.MonadTC._.debugLog1ᵐ
d_debugLog1'7504'_586 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> T_IsMErrorPart_504 -> AgdaAny
d_debugLog1'7504'_586 ~v0 v1 ~v2 v3 v4 ~v5 ~v6 v7 v8
  = du_debugLog1'7504'_586 v1 v3 v4 v7 v8
du_debugLog1'7504'_586 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny -> T_IsMErrorPart_504 -> AgdaAny
du_debugLog1'7504'_586 v0 v1 v2 v3 v4
  = coe
      du_debugLog'7504'_578 (coe v0) (coe v1) (coe v2)
      (coe
         du__'8759''7496''7504'__540 (coe v0) (coe v3) (coe v4)
         (coe
            MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Class.MonadTC._.withAppendDebugPath
d_withAppendDebugPath_590 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
d_withAppendDebugPath_590 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
  = du_withAppendDebugPath_590 v4 v5 v7 v8
du_withAppendDebugPath_590 ::
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
du_withAppendDebugPath_590 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.MonadReader.d_local_40 v0 v1 erased
      (\ v4 ->
         case coe v4 of
           C_TCEnv'46'constructor_205 v5 v6 v7 v8 v9 v10 v11 v12
             -> case coe v12 of
                  C_TCOptions'46'constructor_49 v13 v14
                    -> coe
                         C_TCEnv'46'constructor_205 (coe v5) (coe v6) (coe v7) (coe v8)
                         (coe v9) (coe v10) (coe v11)
                         (coe
                            C_TCOptions'46'constructor_49
                            (coe
                               MAlonzo.Code.Reflection.Debug.C_DebugOptions'46'constructor_1897
                               (coe
                                  MAlonzo.Code.Data.List.Base.du__'8759''691'__448
                                  (coe MAlonzo.Code.Reflection.Debug.d_path_244 (coe v13)) (coe v2))
                               (coe MAlonzo.Code.Reflection.Debug.d_selection_246 (coe v13))
                               (coe MAlonzo.Code.Reflection.Debug.d_filter_248 (coe v13))
                               (coe MAlonzo.Code.Reflection.Debug.d_level_250 (coe v13))
                               (coe MAlonzo.Code.Reflection.Debug.d_prefix_252 (coe v13)))
                            (coe v14))
                  _ -> MAlonzo.RTE.mazUnreachableError
           _ -> MAlonzo.RTE.mazUnreachableError)
      v3
-- Class.MonadTC._.noConstraints
d_noConstraints_604 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_noConstraints_604 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6
  = du_noConstraints_604 v4 v5
du_noConstraints_604 ::
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny -> AgdaAny
du_noConstraints_604 v0 v1
  = coe
      MAlonzo.Code.Class.MonadReader.d_local_40 v0 v1 erased
      (\ v2 ->
         coe
           C_TCEnv'46'constructor_205 (coe d_normalisation_42 (coe v2))
           (coe d_reconstruction_44 (coe v2))
           (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
           (coe d_reduction_48 (coe v2)) (coe d_globalContext_50 (coe v2))
           (coe d_localContext_52 (coe v2)) (coe d_goal_54 (coe v2))
           (coe d_options_56 (coe v2)))
-- Class.MonadTC._.hasType
d_hasType_608 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_hasType_608 ~v0 v1 v2 v3 v4 v5 v6
  = du_hasType_608 v1 v2 v3 v4 v5 v6
du_hasType_608 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_hasType_608 v0 v1 v2 v3 v4 v5
  = coe
      du_isSuccessful_188 (coe v0) (coe v1) (coe v2) (coe ())
      (coe du_noConstraints_604 v3 () (coe d_checkType_138 v2 v4 v5))
-- Class.MonadTC._.hasType'
d_hasType''_614 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_hasType''_614 ~v0 v1 v2 v3 v4 v5 v6
  = du_hasType''_614 v1 v2 v3 v4 v5 v6
du_hasType''_614 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_hasType''_614 v0 v1 v2 v3 v4 v5
  = coe
      du_isSuccessful_188 (coe v0) (coe v1) (coe v2) (coe ())
      (coe
         du_noConstraints_604 v3 ()
         (coe
            MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
            erased
            (coe du_termFromName_218 (coe v0) (coe v1) (coe v2) (coe v4))
            (\ v6 ->
               coe
                 MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                 erased (coe d_checkType_138 v2 v6 v5)
                 (\ v7 ->
                    coe
                      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                      (coe du_isAppliedToUnknownsAndMetas_642 (coe v7))
                      (coe
                         MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                      (coe
                         MAlonzo.Code.Class.MonadError.d_error_26 v1 () erased
                         (coe
                            MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                            (coe ("This makes the function return false" :: Data.Text.Text))
                            (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))
-- Class.MonadTC._._.isUnknownsAndMetas
d_isUnknownsAndMetas_624 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> Bool
d_isUnknownsAndMetas_624 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isUnknownsAndMetas_624 v7
du_isUnknownsAndMetas_624 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> Bool
du_isUnknownsAndMetas_624 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v3 v4
               -> let v5 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v6 v7
                         -> coe du_isUnknownsAndMetas_624 (coe v2)
                       MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216
                         -> coe du_isUnknownsAndMetas_624 (coe v2)
                       _ -> coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC._._.isAppliedToUnknownsAndMetas
d_isAppliedToUnknownsAndMetas_642 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> Bool
d_isAppliedToUnknownsAndMetas_642 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_isAppliedToUnknownsAndMetas_642 v7
du_isAppliedToUnknownsAndMetas_642 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> Bool
du_isAppliedToUnknownsAndMetas_642 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_var_172 v2 v3
           -> coe du_isUnknownsAndMetas_624 (coe v3)
         MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 v2 v3
           -> coe du_isUnknownsAndMetas_624 (coe v3)
         MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 v2 v3
           -> coe du_isUnknownsAndMetas_624 (coe v3)
         MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196 v2 v3
           -> coe du_isUnknownsAndMetas_624 (coe v3)
         MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v2 v3
           -> coe du_isUnknownsAndMetas_624 (coe v3)
         _ -> coe v1)
-- Class.MonadTC._.extendContext
d_extendContext_668 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
d_extendContext_668 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7
  = du_extendContext_668 v4 v5 v7
du_extendContext_668 ::
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
du_extendContext_668 v0 v1 v2
  = coe
      MAlonzo.Code.Class.MonadReader.d_local_40 v0 v1 erased
      (\ v3 ->
         case coe v3 of
           C_TCEnv'46'constructor_205 v4 v5 v6 v7 v8 v9 v10 v11
             -> coe
                  C_TCEnv'46'constructor_205 (coe v4) (coe v5) (coe v6) (coe v7)
                  (coe v8)
                  (coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v9))
                  (coe v10) (coe v11)
           _ -> MAlonzo.RTE.mazUnreachableError)
-- Class.MonadTC._.getContext
d_getContext_678 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 -> AgdaAny
d_getContext_678 ~v0 v1 ~v2 ~v3 v4 = du_getContext_678 v1 v4
du_getContext_678 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 -> AgdaAny
du_getContext_678 v0 v1
  = coe
      MAlonzo.Code.Class.MonadReader.du_reader_46 (coe ()) (coe v0)
      (coe v1) (coe ())
      (coe
         (\ v2 ->
            case coe v2 of
              C_TCEnv'46'constructor_205 v3 v4 v5 v6 v7 v8 v9 v10
                -> coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8) (coe v7)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.MonadTC._.getLocalContext
d_getLocalContext_688 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 -> AgdaAny
d_getLocalContext_688 ~v0 v1 ~v2 ~v3 v4
  = du_getLocalContext_688 v1 v4
du_getLocalContext_688 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 -> AgdaAny
du_getLocalContext_688 v0 v1
  = coe
      MAlonzo.Code.Class.MonadReader.du_reader_46 (coe ()) (coe v0)
      (coe v1) (coe ())
      (coe
         (\ v2 ->
            case coe v2 of
              C_TCEnv'46'constructor_205 v3 v4 v5 v6 v7 v8 v9 v10 -> coe v8
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.MonadTC._.inContext
d_inContext_696 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
d_inContext_696 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7
  = du_inContext_696 v4 v5 v7
du_inContext_696 ::
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_inContext_696 v0 v1 v2
  = coe
      MAlonzo.Code.Class.MonadReader.d_local_40 v0 v1 erased
      (\ v3 ->
         coe
           C_TCEnv'46'constructor_205 (coe d_normalisation_42 (coe v3))
           (coe d_reconstruction_44 (coe v3))
           (coe d_noConstraints_46 (coe v3)) (coe d_reduction_48 (coe v3))
           (coe d_globalContext_50 (coe v3)) (coe v2) (coe d_goal_54 (coe v3))
           (coe d_options_56 (coe v3)))
-- Class.MonadTC._.extendContext'
d_extendContext''_702 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
d_extendContext''_702 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
  = du_extendContext''_702 v4 v5 v7 v8
du_extendContext''_702 ::
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_extendContext''_702 v0 v1 v2 v3
  = case coe v2 of
      [] -> coe v3
      (:) v4 v5
        -> coe
             du_extendContext_668 v0 v1 v4
             (coe du_extendContext''_702 (coe v0) (coe v1) (coe v5) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC._.dropContext
d_dropContext_712 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> AgdaAny -> AgdaAny
d_dropContext_712 ~v0 v1 ~v2 ~v3 v4 v5 ~v6 v7 v8
  = du_dropContext_712 v1 v4 v5 v7 v8
du_dropContext_712 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer -> AgdaAny -> AgdaAny
du_dropContext_712 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased v2
      erased (coe du_getContext_678 (coe v0) (coe v1))
      (\ v5 ->
         coe
           du_inContext_696 v1 v2
           (coe MAlonzo.Code.Data.List.Base.du_drop_542 (coe v3) (coe v5)) v4)
-- Class.MonadTC._.logAndError
d_logAndError_720 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] -> AgdaAny
d_logAndError_720 ~v0 v1 v2 v3 v4 v5 ~v6 v7
  = du_logAndError_720 v1 v2 v3 v4 v5 v7
du_logAndError_720 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] -> AgdaAny
du_logAndError_720 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
      (coe v4) (coe du_debugLog_570 (coe v0) (coe v2) (coe v3) (coe v5))
      (coe MAlonzo.Code.Class.MonadError.d_error_26 v1 v4 erased v5)
-- Class.MonadTC._.error1
d_error1_724 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Reflection.Debug.T_IsErrorPart_6 -> AgdaAny -> AgdaAny
d_error1_724 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9
  = du_error1_724 v2 v6 v8 v9
du_error1_724 ::
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Reflection.Debug.T_IsErrorPart_6 -> AgdaAny -> AgdaAny
du_error1_724 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.MonadError.d_error_26 v0 v1 erased
      (coe
         MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v3)
         (coe v2) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Class.MonadTC._.debugLog1
d_debugLog1_728 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  () ->
  MAlonzo.Code.Reflection.Debug.T_IsErrorPart_6 -> AgdaAny -> AgdaAny
d_debugLog1_728 ~v0 v1 ~v2 v3 v4 ~v5 v6 v7
  = du_debugLog1_728 v1 v3 v4 v6 v7
du_debugLog1_728 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Reflection.Debug.T_IsErrorPart_6 -> AgdaAny -> AgdaAny
du_debugLog1_728 v0 v1 v2 v3 v4
  = coe
      du_debugLog_570 (coe v0) (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v4)
         (coe v3) (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Class.MonadTC._.logAndError1
d_logAndError1_732 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Reflection.Debug.T_IsErrorPart_6 -> AgdaAny -> AgdaAny
d_logAndError1_732 ~v0 v1 v2 v3 v4 ~v5 v6 ~v7 v8 v9
  = du_logAndError1_732 v1 v2 v3 v4 v6 v8 v9
du_logAndError1_732 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Reflection.Debug.T_IsErrorPart_6 -> AgdaAny -> AgdaAny
du_logAndError1_732 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
      (coe v4)
      (coe du_debugLog1_728 (coe v0) (coe v2) (coe v3) (coe v5) (coe v6))
      (coe du_error1_724 (coe v1) (coe v4) (coe v5) (coe v6))
-- Class.MonadTC._.markDontFail
d_markDontFail_736 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
d_markDontFail_736 ~v0 v1 v2 v3 v4 v5 ~v6 v7 v8
  = du_markDontFail_736 v1 v2 v3 v4 v5 v7 v8
du_markDontFail_736 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
du_markDontFail_736 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Class.MonadError.d_catch_28 v1 v4 erased v6
      (\ v7 ->
         coe
           du_logAndError_720 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
           (coe
              MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v5)
              (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
              (coe
                 MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                 (coe
                    (" should never fail! This is a bug!\nError:\n" :: Data.Text.Text))
                 (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                 (coe v7))))
-- Class.MonadTC._.goalTy
d_goalTy_744 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 -> AgdaAny
d_goalTy_744 ~v0 v1 ~v2 v3 v4 = du_goalTy_744 v1 v3 v4
du_goalTy_744 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 -> AgdaAny
du_goalTy_744 v0 v1 v2
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased
      (coe
         MAlonzo.Code.Class.MonadReader.du_reader_46 (coe ()) (coe v0)
         (coe v2) (coe ()) (coe (\ v3 -> d_goal_54 (coe v3))))
      (\ v3 ->
         case coe v3 of
           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
             -> coe d_inferType_136 v1 v4
           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
             -> coe MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased v4
           _ -> MAlonzo.RTE.mazUnreachableError)
-- Class.MonadTC._.runSpeculativeMaybe
d_runSpeculativeMaybe_752 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> AgdaAny -> AgdaAny
d_runSpeculativeMaybe_752 ~v0 v1 ~v2 v3 ~v4 v5 ~v6 v7 v8
  = du_runSpeculativeMaybe_752 v1 v3 v5 v7 v8
du_runSpeculativeMaybe_752 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_runSpeculativeMaybe_752 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 v2 erased v2
      erased
      (coe
         d_runSpeculative_172 v1 v2 erased
         (coe
            MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
            (MAlonzo.Code.Class.Applicative.Core.d_super_18
               (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
            v2 erased v2 erased
            (coe
               MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112
               (coe (\ v5 -> v5))
               (coe MAlonzo.Code.Data.Maybe.Base.du_is'45'just_20))
            v3))
      (\ v5 ->
         case coe v5 of
           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
             -> coe MAlonzo.Code.Class.Monad.Core.d_return_20 v0 v2 erased v6
           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
           _ -> MAlonzo.RTE.mazUnreachableError)
-- Class.MonadTC._.try
d_try_762 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  [AgdaAny] -> AgdaAny -> AgdaAny
d_try_762 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 = du_try_762 v2 v5 v6
du_try_762 ::
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  [AgdaAny] -> AgdaAny -> AgdaAny
du_try_762 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Class.MonadError.d_catch_28 v0 () erased v3
             (\ v5 -> coe du_try_762 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadTC._.getConstrs
d_getConstrs_774 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny -> AgdaAny
d_getConstrs_774 ~v0 v1 v2 v3 ~v4 v5
  = du_getConstrs_774 v1 v2 v3 v5
du_getConstrs_774 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 -> AgdaAny -> AgdaAny
du_getConstrs_774 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe d_getDefinition_162 v2 v3)
      (\ v4 ->
         coe
           MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
           erased
           (let v5
                  = coe
                      MAlonzo.Code.Class.MonadError.d_error_26 v1 () erased
                      (coe
                         MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v3)
                         (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Name_22)
                         (coe
                            MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                            (coe ("is not a data or record definition!" :: Data.Text.Text))
                            (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))) in
            coe
              (case coe v4 of
                 MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'type_290 v6 v7
                   -> coe MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased v7
                 MAlonzo.Code.Agda.Builtin.Reflection.C_record'45'type_296 v6 v7
                   -> coe
                        MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                        (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v6))
                 _ -> coe v5))
           (\ v5 ->
              coe
                MAlonzo.Code.Class.Traversable.Core.du_traverse_44
                (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
                (coe
                   MAlonzo.Code.Class.Traversable.Instances.d_TraversableM'45'List_28)
                (coe ()) (coe ()) (coe v0)
                (coe
                   (\ v6 ->
                      coe
                        MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
                        (MAlonzo.Code.Class.Applicative.Core.d_super_18
                           (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
                        () erased () erased
                        (\ v7 ->
                           coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v7))
                        (coe
                           MAlonzo.Code.Class.Monad.Core.du__'61''60''60'__32 (coe v0)
                           (coe ()) (coe ()) (coe d_normalise_140 (coe v2))
                           (coe d_getType_160 v2 v6))))
                (coe v5)))
-- Class.MonadTC._.getConstrsForType
d_getConstrsForType_796 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_getConstrsForType_796 ~v0 v1 v2 v3 ~v4 v5
  = du_getConstrsForType_796 v1 v2 v3 v5
du_getConstrsForType_796 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_getConstrsForType_796 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe d_normalise_140 v2 v3)
      (\ v4 ->
         let v5
               = coe
                   MAlonzo.Code.Class.MonadError.d_error_26 v1 () erased
                   (coe
                      MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v3)
                      (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                      (coe
                         MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                         (coe ("does not reduce to a definition!" :: Data.Text.Text))
                         (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))) in
         coe
           (case coe v4 of
              MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 v6 v7
                -> coe du_getConstrs_774 (coe v0) (coe v1) (coe v2) (coe v6)
              _ -> coe v5))
-- Class.MonadTC._.getConstrsForTerm
d_getConstrsForTerm_804 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_getConstrsForTerm_804 ~v0 v1 v2 v3 ~v4 v5
  = du_getConstrsForTerm_804 v1 v2 v3 v5
du_getConstrsForTerm_804 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_getConstrsForTerm_804 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'61''60''60'__32 (coe v0)
      (coe ()) (coe ())
      (coe du_getConstrsForType_796 (coe v0) (coe v1) (coe v2))
      (coe d_inferType_136 v2 v3)
-- Class.MonadTC._.withPattern
d_withPattern_808 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  AgdaAny -> AgdaAny
d_withPattern_808 ~v0 v1 ~v2 ~v3 v4 v5 v6 v7
  = du_withPattern_808 v1 v4 v5 v6 v7
du_withPattern_808 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  AgdaAny -> AgdaAny
du_withPattern_808 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
      (MAlonzo.Code.Class.Applicative.Core.d_super_18
         (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
      () erased () erased
      (coe
         MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272 (coe v2)
         (coe v3))
      (coe du_extendContext''_702 (coe v1) (coe ()) (coe v2) (coe v4))
-- Class.MonadTC._.unifyWithGoal
d_unifyWithGoal_816 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_unifyWithGoal_816 ~v0 v1 v2 v3 v4 v5
  = du_unifyWithGoal_816 v1 v2 v3 v4 v5
du_unifyWithGoal_816 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_unifyWithGoal_816 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased
      (coe
         MAlonzo.Code.Class.MonadReader.du_reader_46 (coe ()) (coe v0)
         (coe v3) (coe ()) (coe (\ v5 -> d_goal_54 (coe v5))))
      (\ v5 ->
         let v6
               = coe
                   du_error1_724 (coe v1) (coe ())
                   (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                   (coe ("unifyWithGoal: Goal is not a term!" :: Data.Text.Text)) in
         coe
           (case coe v5 of
              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
                -> coe d_unify_132 v2 v7 v4
              _ -> coe v6))
-- Class.MonadTC._.runWithHole
d_runWithHole_824 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  AgdaAny -> AgdaAny
d_runWithHole_824 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7
  = du_runWithHole_824 v4 v5 v7
du_runWithHole_824 ::
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  AgdaAny -> AgdaAny
du_runWithHole_824 v0 v1 v2
  = coe
      MAlonzo.Code.Class.MonadReader.d_local_40 v0 v1 erased
      (\ v3 ->
         coe
           C_TCEnv'46'constructor_205 (coe d_normalisation_42 (coe v3))
           (coe d_reconstruction_44 (coe v3))
           (coe d_noConstraints_46 (coe v3)) (coe d_reduction_48 (coe v3))
           (coe d_globalContext_50 (coe v3)) (coe d_localContext_52 (coe v3))
           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v2))
           (coe d_options_56 (coe v3)))
-- Class.MonadTC._.runWithGoalTy
d_runWithGoalTy_830 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  AgdaAny -> AgdaAny
d_runWithGoalTy_830 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 v7
  = du_runWithGoalTy_830 v4 v5 v7
du_runWithGoalTy_830 ::
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  AgdaAny -> AgdaAny
du_runWithGoalTy_830 v0 v1 v2
  = coe
      MAlonzo.Code.Class.MonadReader.d_local_40 v0 v1 erased
      (\ v3 ->
         coe
           C_TCEnv'46'constructor_205 (coe d_normalisation_42 (coe v3))
           (coe d_reconstruction_44 (coe v3))
           (coe d_noConstraints_46 (coe v3)) (coe d_reduction_48 (coe v3))
           (coe d_globalContext_50 (coe v3)) (coe d_localContext_52 (coe v3))
           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v2))
           (coe d_options_56 (coe v3)))
-- Class.MonadTC._.goalHole
d_goalHole_836 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 -> AgdaAny
d_goalHole_836 ~v0 v1 ~v2 v3 v4 = du_goalHole_836 v1 v3 v4
du_goalHole_836 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 -> AgdaAny
du_goalHole_836 v0 v1 v2
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased
      (coe
         MAlonzo.Code.Class.MonadReader.du_reader_46 (coe ()) (coe v0)
         (coe v2) (coe ()) (coe (\ v3 -> d_goal_54 (coe v3))))
      (\ v3 ->
         case coe v3 of
           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
             -> coe MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased v4
           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
             -> coe du_newMeta_392 v1 v4
           _ -> MAlonzo.RTE.mazUnreachableError)
-- Class.MonadTC._.withGoalHole
d_withGoalHole_844 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny -> AgdaAny
d_withGoalHole_844 ~v0 v1 ~v2 v3 v4 v5
  = du_withGoalHole_844 v1 v3 v4 v5
du_withGoalHole_844 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny -> AgdaAny
du_withGoalHole_844 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe du_goalHole_836 (coe v0) (coe v1) (coe v2))
      (\ v4 ->
         coe
           MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
           (coe ()) (coe du_runWithHole_824 v2 () v4 v3)
           (coe MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased v4))
-- Class.MonadTC._.findInstances
d_findInstances_850 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_findInstances_850 ~v0 v1 v2 v3 v4 v5
  = du_findInstances_850 v1 v2 v3 v4 v5
du_findInstances_850 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_findInstances_850 v0 v1 v2 v3 v4
  = coe
      du_runAndReset_182 (coe v0) (coe v2) (coe ())
      (coe
         MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
         erased
         (coe
            MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
            (MAlonzo.Code.Class.Applicative.Core.d_super_18
               (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
            () erased () erased
            (coe du_findMeta_858 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
            (coe du_newMeta_392 v2 v4))
         (\ v5 ->
            let v6
                  = coe
                      du_error1_724 (coe v1) (coe ())
                      (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                      (coe
                         ("[findInstances] newMeta did not produce meta-variable!"
                          ::
                          Data.Text.Text)) in
            coe
              (case coe v5 of
                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                   -> coe d_getInstances_174 v2 v7
                 _ -> coe v6)))
-- Class.MonadTC._._.findMeta
d_findMeta_858 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> Maybe AgdaAny
d_findMeta_858 ~v0 v1 v2 v3 v4 v5 = du_findMeta_858 v1 v2 v3 v4 v5
du_findMeta_858 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> Maybe AgdaAny
du_findMeta_858 v0 v1 v2 v3 v4
  = coe
      du_'46'extendedlambda10_860 (coe v0) (coe v1) (coe v2) (coe v3)
      (coe v4)
-- Class.MonadTC._._..extendedlambda10
d_'46'extendedlambda10_860 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> Maybe AgdaAny
d_'46'extendedlambda10_860 ~v0 v1 v2 v3 v4 v5 v6
  = du_'46'extendedlambda10_860 v1 v2 v3 v4 v5 v6
du_'46'extendedlambda10_860 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  T_MonadTC_80 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> Maybe AgdaAny
du_'46'extendedlambda10_860 v0 v1 v2 v3 v4 v5
  = let v6 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v5 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_lam_190 v7 v8
           -> case coe v8 of
                MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v9 v10
                  -> coe du_findMeta_858 v0 v1 v2 v3 v4 v10
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202 v7 v8
           -> case coe v7 of
                MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v9 v10
                  -> case coe v8 of
                       MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v11 v12
                         -> coe
                              MAlonzo.Code.Data.Maybe.Base.du__'60''8739''62'__80
                              (coe du_findMeta_858 v0 v1 v2 v3 v4 v10)
                              (coe du_findMeta_858 v0 v1 v2 v3 v4 v12)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v7 v8
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v7)
         _ -> coe v6)
-- Class.MonadTC.MonadTC-TC
d_MonadTC'45'TC_874 :: T_MonadTC_80
d_MonadTC'45'TC_874
  = coe
      C_MonadTC'46'constructor_5621
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_unify_338)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_typeError_344)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_inferType_346)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_checkType_348)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_normalise_350)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_reduce_352)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_quoteTC_364)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_unquoteTC_370)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_quoteωTC_374)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_freshName_390)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_declareDef_392)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_declarePostulate_394)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_defineFun_404)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_getType_406)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_getDefinition_408)
      (\ v0 v1 v2 ->
         coe MAlonzo.Code.Agda.Builtin.Reflection.du_blockOnMeta_626 v0 v2)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_commitTC_416)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_isMacro_418)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_debugPrint_462)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_runSpeculative_482)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_getInstances_484)
