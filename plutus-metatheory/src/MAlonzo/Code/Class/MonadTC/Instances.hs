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

module MAlonzo.Code.Class.MonadTC.Instances where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Monad.Core
import qualified MAlonzo.Code.Class.MonadError
import qualified MAlonzo.Code.Class.MonadTC

-- Class.MonadTC.Instances._.blockOnMeta
d_blockOnMeta_8 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_blockOnMeta_8 v0
  = coe MAlonzo.Code.Class.MonadTC.d_blockOnMeta_164 (coe v0)
-- Class.MonadTC.Instances._.checkType
d_checkType_10 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_checkType_10 v0
  = coe MAlonzo.Code.Class.MonadTC.d_checkType_138 (coe v0)
-- Class.MonadTC.Instances._.commitTC
d_commitTC_12 :: MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny
d_commitTC_12 v0
  = coe MAlonzo.Code.Class.MonadTC.d_commitTC_166 (coe v0)
-- Class.MonadTC.Instances._.debugPrint
d_debugPrint_14 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] -> AgdaAny
d_debugPrint_14 v0
  = coe MAlonzo.Code.Class.MonadTC.d_debugPrint_170 (coe v0)
-- Class.MonadTC.Instances._.declareAndDefineFun
d_declareAndDefineFun_16 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
d_declareAndDefineFun_16 ~v0 v1 ~v2 v3
  = du_declareAndDefineFun_16 v1 v3
du_declareAndDefineFun_16 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
du_declareAndDefineFun_16 v0 v1
  = coe
      MAlonzo.Code.Class.MonadTC.du_declareAndDefineFun_384 (coe v0)
      (coe v1)
-- Class.MonadTC.Instances._.declareAndDefineFuns
d_declareAndDefineFuns_18 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_declareAndDefineFuns_18 ~v0 v1 ~v2 v3
  = du_declareAndDefineFuns_18 v1 v3
du_declareAndDefineFuns_18 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_declareAndDefineFuns_18 v0 v1
  = coe
      MAlonzo.Code.Class.MonadTC.du_declareAndDefineFuns_334 (coe v0)
      (coe v1)
-- Class.MonadTC.Instances._.declareAndDefineFunsDebug
d_declareAndDefineFunsDebug_20 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_declareAndDefineFunsDebug_20 ~v0 v1 v2 v3
  = du_declareAndDefineFunsDebug_20 v1 v2 v3
du_declareAndDefineFunsDebug_20 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_declareAndDefineFunsDebug_20 v0 v1 v2
  = coe
      MAlonzo.Code.Class.MonadTC.du_declareAndDefineFunsDebug_350
      (coe v0) (coe v1) (coe v2)
-- Class.MonadTC.Instances._.declareDef
d_declareDef_22 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_declareDef_22 v0
  = coe MAlonzo.Code.Class.MonadTC.d_declareDef_154 (coe v0)
-- Class.MonadTC.Instances._.declarePostulate
d_declarePostulate_24 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_declarePostulate_24 v0
  = coe MAlonzo.Code.Class.MonadTC.d_declarePostulate_156 (coe v0)
-- Class.MonadTC.Instances._.defineFun
d_defineFun_26 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
d_defineFun_26 v0
  = coe MAlonzo.Code.Class.MonadTC.d_defineFun_158 (coe v0)
-- Class.MonadTC.Instances._.freshName
d_freshName_28 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_freshName_28 v0
  = coe MAlonzo.Code.Class.MonadTC.d_freshName_152 (coe v0)
-- Class.MonadTC.Instances._.getDefinition
d_getDefinition_30 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_getDefinition_30 v0
  = coe MAlonzo.Code.Class.MonadTC.d_getDefinition_162 (coe v0)
-- Class.MonadTC.Instances._.getInstances
d_getInstances_32 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_getInstances_32 v0
  = coe MAlonzo.Code.Class.MonadTC.d_getInstances_174 (coe v0)
-- Class.MonadTC.Instances._.getType
d_getType_34 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_getType_34 v0
  = coe MAlonzo.Code.Class.MonadTC.d_getType_160 (coe v0)
-- Class.MonadTC.Instances._.hasUnsolvedMetas
d_hasUnsolvedMetas_36 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_hasUnsolvedMetas_36 ~v0 v1 v2 v3
  = du_hasUnsolvedMetas_36 v1 v2 v3
du_hasUnsolvedMetas_36 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_hasUnsolvedMetas_36 v0 v1 v2
  = coe
      MAlonzo.Code.Class.MonadTC.du_hasUnsolvedMetas_246 (coe v0)
      (coe v1) (coe v2)
-- Class.MonadTC.Instances._.hasUnsolvedMetas'
d_hasUnsolvedMetas''_38 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
d_hasUnsolvedMetas''_38 ~v0 v1 v2 v3
  = du_hasUnsolvedMetas''_38 v1 v2 v3
du_hasUnsolvedMetas''_38 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
du_hasUnsolvedMetas''_38 v0 v1 v2
  = coe
      MAlonzo.Code.Class.MonadTC.du_hasUnsolvedMetas''_248 (coe v0)
      (coe v1) (coe v2)
-- Class.MonadTC.Instances._.hasUnsolvedMetasCl
d_hasUnsolvedMetasCl_40 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
d_hasUnsolvedMetasCl_40 ~v0 v1 v2 v3
  = du_hasUnsolvedMetasCl_40 v1 v2 v3
du_hasUnsolvedMetasCl_40 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] -> AgdaAny
du_hasUnsolvedMetasCl_40 v0 v1 v2
  = coe
      MAlonzo.Code.Class.MonadTC.du_hasUnsolvedMetasCl_250 (coe v0)
      (coe v1) (coe v2)
-- Class.MonadTC.Instances._.hasUnsolvedMetasTel
d_hasUnsolvedMetasTel_42 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_hasUnsolvedMetasTel_42 ~v0 v1 v2 v3
  = du_hasUnsolvedMetasTel_42 v1 v2 v3
du_hasUnsolvedMetasTel_42 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_hasUnsolvedMetasTel_42 v0 v1 v2
  = coe
      MAlonzo.Code.Class.MonadTC.du_hasUnsolvedMetasTel_252 (coe v0)
      (coe v1) (coe v2)
-- Class.MonadTC.Instances._.inferType
d_inferType_44 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_inferType_44 v0
  = coe MAlonzo.Code.Class.MonadTC.d_inferType_136 (coe v0)
-- Class.MonadTC.Instances._.isCon
d_isCon_46 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_isCon_46 ~v0 v1 ~v2 v3 = du_isCon_46 v1 v3
du_isCon_46 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
du_isCon_46 v0 v1
  = coe MAlonzo.Code.Class.MonadTC.du_isCon_200 (coe v0) (coe v1)
-- Class.MonadTC.Instances._.isDef
d_isDef_48 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_isDef_48 ~v0 v1 ~v2 v3 = du_isDef_48 v1 v3
du_isDef_48 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
du_isDef_48 v0 v1
  = coe MAlonzo.Code.Class.MonadTC.du_isDef_194 (coe v0) (coe v1)
-- Class.MonadTC.Instances._.isMacro
d_isMacro_50 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_isMacro_50 v0
  = coe MAlonzo.Code.Class.MonadTC.d_isMacro_168 (coe v0)
-- Class.MonadTC.Instances._.isSolvedMeta
d_isSolvedMeta_52 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_isSolvedMeta_52 ~v0 v1 v2 v3 = du_isSolvedMeta_52 v1 v2 v3
du_isSolvedMeta_52 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_isSolvedMeta_52 v0 v1 v2
  = coe
      MAlonzo.Code.Class.MonadTC.du_isSolvedMeta_232 (coe v0) (coe v1)
      (coe v2)
-- Class.MonadTC.Instances._.isSuccessful
d_isSuccessful_54 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_isSuccessful_54 ~v0 v1 v2 v3 = du_isSuccessful_54 v1 v2 v3
du_isSuccessful_54 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
du_isSuccessful_54 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Class.MonadTC.du_isSuccessful_188 (coe v0) (coe v1)
      (coe v2) v3 v5
-- Class.MonadTC.Instances._.mkRecord
d_mkRecord_56 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
d_mkRecord_56 ~v0 v1 v2 v3 = du_mkRecord_56 v1 v2 v3
du_mkRecord_56 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
du_mkRecord_56 v0 v1 v2
  = coe
      MAlonzo.Code.Class.MonadTC.du_mkRecord_222 (coe v0) (coe v1)
      (coe v2)
-- Class.MonadTC.Instances._.nameConstr
d_nameConstr_58 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
d_nameConstr_58 ~v0 v1 v2 v3 = du_nameConstr_58 v1 v2 v3
du_nameConstr_58 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> AgdaAny
du_nameConstr_58 v0 v1 v2
  = coe
      MAlonzo.Code.Class.MonadTC.du_nameConstr_206 (coe v0) (coe v1)
      (coe v2)
-- Class.MonadTC.Instances._.newMeta
d_newMeta_60 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_newMeta_60 ~v0 ~v1 ~v2 v3 = du_newMeta_60 v3
du_newMeta_60 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_newMeta_60 v0
  = coe MAlonzo.Code.Class.MonadTC.du_newMeta_392 (coe v0)
-- Class.MonadTC.Instances._.normalise
d_normalise_62 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_normalise_62 v0
  = coe MAlonzo.Code.Class.MonadTC.d_normalise_140 (coe v0)
-- Class.MonadTC.Instances._.quoteTC
d_quoteTC_64 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_quoteTC_64 v0
  = coe MAlonzo.Code.Class.MonadTC.d_quoteTC_144 (coe v0)
-- Class.MonadTC.Instances._.quoteωTC
d_quoteωTC_66 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> () -> AgdaAny -> AgdaAny
d_quoteωTC_66 v0
  = coe MAlonzo.Code.Class.MonadTC.d_quoteωTC_150 (coe v0)
-- Class.MonadTC.Instances._.reduce
d_reduce_68 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_reduce_68 v0
  = coe MAlonzo.Code.Class.MonadTC.d_reduce_142 (coe v0)
-- Class.MonadTC.Instances._.runAndReset
d_runAndReset_70 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_runAndReset_70 ~v0 v1 ~v2 v3 = du_runAndReset_70 v1 v3
du_runAndReset_70 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
du_runAndReset_70 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.MonadTC.du_runAndReset_182 (coe v0) (coe v1) v2
      v4
-- Class.MonadTC.Instances._.runSpeculative
d_runSpeculative_72 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_runSpeculative_72 v0
  = coe MAlonzo.Code.Class.MonadTC.d_runSpeculative_172 (coe v0)
-- Class.MonadTC.Instances._.termFromName
d_termFromName_74 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_termFromName_74 ~v0 v1 v2 v3 = du_termFromName_74 v1 v2 v3
du_termFromName_74 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
du_termFromName_74 v0 v1 v2
  = coe
      MAlonzo.Code.Class.MonadTC.du_termFromName_218 (coe v0) (coe v1)
      (coe v2)
-- Class.MonadTC.Instances._.typeError
d_typeError_76 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] -> AgdaAny
d_typeError_76 v0
  = coe MAlonzo.Code.Class.MonadTC.d_typeError_134 (coe v0)
-- Class.MonadTC.Instances._.unify
d_unify_78 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_unify_78 v0 = coe MAlonzo.Code.Class.MonadTC.d_unify_132 (coe v0)
-- Class.MonadTC.Instances._.unquoteTC
d_unquoteTC_80 ::
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_unquoteTC_80 v0
  = coe MAlonzo.Code.Class.MonadTC.d_unquoteTC_146 (coe v0)
