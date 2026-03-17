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

module MAlonzo.Code.Reflection.Utils.TCM where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Monad.Instances
import qualified MAlonzo.Code.Class.MonadError
import qualified MAlonzo.Code.Class.MonadReader
import qualified MAlonzo.Code.Class.MonadTC
import qualified MAlonzo.Code.Reflection.Utils.TCI

-- Reflection.Utils.TCM._._-∗-_
d__'45''8727''45'__12 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
d__'45''8727''45'__12
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du__'45''8727''45'__114
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._._-∙-_
d__'45''8729''45'__14 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d__'45''8729''45'__14
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du__'45''8729''45'__106
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.apply
d_apply_16 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
d_apply_16
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_apply_28
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.applyWithVisibility
d_applyWithVisibility_18 ::
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
d_applyWithVisibility_18
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_applyWithVisibility_476
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.applyWithVisibilityDB
d_applyWithVisibilityDB_20 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
d_applyWithVisibilityDB_20
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_applyWithVisibilityDB_490
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.compatible?
d_compatible'63'_22 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_compatible'63'_22
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_compatible'63'_242
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.ensureNoMetas
d_ensureNoMetas_24 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_ensureNoMetas_24
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_ensureNoMetas_128
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.fresh-level
d_fresh'45'level_26 :: AgdaAny
d_fresh'45'level_26
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_fresh'45'level_18
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.getDataDef
d_getDataDef_28 :: AgdaAny -> AgdaAny
d_getDataDef_28
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_getDataDef_374
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.getDataOrRecordDef
d_getDataOrRecordDef_30 :: AgdaAny -> AgdaAny
d_getDataOrRecordDef_30
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_getDataOrRecordDef_404
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.getFuel
d_getFuel_32 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_getFuel_32
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_getFuel_422
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
-- Reflection.Utils.TCM._.getParams
d_getParams_34 :: AgdaAny -> AgdaAny
d_getParams_34
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_getParams_412
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.getParamsAndIndices
d_getParamsAndIndices_36 :: AgdaAny -> AgdaAny
d_getParamsAndIndices_36
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_getParamsAndIndices_416
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.getRecordDef
d_getRecordDef_38 :: AgdaAny -> AgdaAny
d_getRecordDef_38
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_getRecordDef_392
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.getType'
d_getType''_40 :: AgdaAny -> AgdaAny
d_getType''_40
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_getType''_366
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.getTypeDB
d_getTypeDB_42 :: Integer -> AgdaAny
d_getTypeDB_42
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_getTypeDB_370
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.inDebugPath
d_inDebugPath_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
d_inDebugPath_44 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_inDebugPath_318
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v4 v5 v6 v7 -> v7)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874) v0 v2 v3
-- Reflection.Utils.TCM._.instantiate
d_instantiate_46 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_instantiate_46
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_instantiate_126
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.isDefT
d_isDefT_48 ::
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_isDefT_48
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_isDefT_458
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.isNArySort
d_isNArySort_50 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_isNArySort_50
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_isNArySort_446
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.isSort
d_isSort_52 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_isSort_52
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_isSort_440
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.logContext
d_logContext_54 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_logContext_54
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_logContext_286
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.logCurrentContext
d_logCurrentContext_56 :: AgdaAny
d_logCurrentContext_56
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_logCurrentContext_316
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.logTelescope
d_logTelescope_58 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_logTelescope_58
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_logTelescope_254
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.printTerm
d_printTerm_60 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_printTerm_60
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_printTerm_210
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.unifyStrict
d_unifyStrict_62 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_unifyStrict_62
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_unifyStrict_200
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.unifyStricts
d_unifyStricts_64 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
d_unifyStricts_64
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_unifyStricts_230
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.viewAndReduceTy
d_viewAndReduceTy_66 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_viewAndReduceTy_66
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_viewAndReduceTy_324
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.withHole
d_withHole_68 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  (MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny) ->
  AgdaAny
d_withHole_68
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_withHole_20
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.withSafeReset
d_withSafeReset_70 :: AgdaAny -> AgdaAny
d_withSafeReset_70
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_withSafeReset_468
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.NewMeta.unifyStrict
d_unifyStrict_74 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_unifyStrict_74
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_unifyStrict_200
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
-- Reflection.Utils.TCM._.NoMeta.unifyStrict
d_unifyStrict_78 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_unifyStrict_78
  = coe
      MAlonzo.Code.Reflection.Utils.TCI.du_unifyStrict_220
      (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6)
      (coe MAlonzo.Code.Class.MonadError.d_MonadError'45'TC_30)
      (coe
         MAlonzo.Code.Class.MonadReader.C_MonadReader'46'constructor_305
         (coe MAlonzo.Code.Class.MonadTC.d_initTCEnv_70)
         (coe (\ v0 v1 v2 v3 -> v3)))
      (coe MAlonzo.Code.Class.MonadTC.d_MonadTC'45'TC_874)
