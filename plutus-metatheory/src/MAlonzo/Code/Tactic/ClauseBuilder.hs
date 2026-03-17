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

module MAlonzo.Code.Tactic.ClauseBuilder where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Applicative.Core
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Class.DecEq.Instances
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Class.Functor.Instances
import qualified MAlonzo.Code.Class.Monad.Core
import qualified MAlonzo.Code.Class.Monad.Id
import qualified MAlonzo.Code.Class.Monad.Instances
import qualified MAlonzo.Code.Class.MonadError
import qualified MAlonzo.Code.Class.MonadReader
import qualified MAlonzo.Code.Class.MonadTC
import qualified MAlonzo.Code.Class.Traversable.Core
import qualified MAlonzo.Code.Class.Traversable.Instances
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.NonEmpty.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous
import qualified MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional
import qualified MAlonzo.Code.Data.List.Relation.Unary.Linked
import qualified MAlonzo.Code.Data.List.Sort.Base
import qualified MAlonzo.Code.Data.List.Sort.MergeSort.Base
import qualified MAlonzo.Code.Data.List.Sort.MergeSort.Properties
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Meta.Init
import qualified MAlonzo.Code.Meta.Prelude
import qualified MAlonzo.Code.Reflection.AST.Argument
import qualified MAlonzo.Code.Reflection.Debug
import qualified MAlonzo.Code.Reflection.QQuotedDefinitions
import qualified MAlonzo.Code.Reflection.Utils.Core
import qualified MAlonzo.Code.Reflection.Utils.Substitute
import qualified MAlonzo.Code.Reflection.Utils.TCI
import qualified MAlonzo.Code.Relation.Binary.Bundles

-- Tactic.ClauseBuilder._.sort
d_sort_6 :: [Integer] -> [Integer]
d_sort_6
  = coe
      MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_sort_166
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'decTotalOrder_2882)
-- Tactic.ClauseBuilder._.sort-↗
d_sort'45''8599'_8 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_sort'45''8599'_8
  = coe
      MAlonzo.Code.Data.List.Sort.MergeSort.Properties.du_sort'45''8599'_230
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'decTotalOrder_2882)
-- Tactic.ClauseBuilder._.sort-↭
d_sort'45''8621'_10 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_sort'45''8621'_10
  = coe
      MAlonzo.Code.Data.List.Sort.MergeSort.Properties.du_sort'45''8621'_192
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'decTotalOrder_2882)
-- Tactic.ClauseBuilder._.sort-↭ₛ
d_sort'45''8621''8347'_12 ::
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_sort'45''8621''8347'_12
  = let v0
          = MAlonzo.Code.Data.Nat.Properties.d_'8804''45'decTotalOrder_2882 in
    coe
      (coe
         MAlonzo.Code.Data.List.Sort.Base.du_sort'45''8621''8347'_260
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.du_totalOrder_1160 (coe v0))
         (coe
            MAlonzo.Code.Data.List.Sort.MergeSort.Properties.du_mergeSort_236
            (coe
               MAlonzo.Code.Data.Nat.Properties.d_'8804''45'decTotalOrder_2882)))
-- Tactic.ClauseBuilder.ClauseBuilder
d_ClauseBuilder_20 a0 = ()
data T_ClauseBuilder_20
  = C_ClauseBuilder'46'constructor_351 (() -> AgdaAny -> AgdaAny)
                                       (() ->
                                        [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
                                        MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
                                        AgdaAny -> AgdaAny)
                                       (AgdaAny -> AgdaAny)
-- Tactic.ClauseBuilder.ClauseBuilder.Base
d_Base_32 :: T_ClauseBuilder_20 -> () -> ()
d_Base_32 = erased
-- Tactic.ClauseBuilder.ClauseBuilder.liftBase
d_liftBase_34 :: T_ClauseBuilder_20 -> () -> AgdaAny -> AgdaAny
d_liftBase_34 v0
  = case coe v0 of
      C_ClauseBuilder'46'constructor_351 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.ClauseBuilder.addPattern
d_addPattern_36 ::
  T_ClauseBuilder_20 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 -> AgdaAny -> AgdaAny
d_addPattern_36 v0
  = case coe v0 of
      C_ClauseBuilder'46'constructor_351 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.ClauseBuilder.toClause
d_toClause_38 :: T_ClauseBuilder_20 -> AgdaAny -> AgdaAny
d_toClause_38 v0
  = case coe v0 of
      C_ClauseBuilder'46'constructor_351 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder._.Base
d_Base_42 :: T_ClauseBuilder_20 -> () -> ()
d_Base_42 = erased
-- Tactic.ClauseBuilder._.addPattern
d_addPattern_44 ::
  T_ClauseBuilder_20 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 -> AgdaAny -> AgdaAny
d_addPattern_44 v0 = coe d_addPattern_36 (coe v0)
-- Tactic.ClauseBuilder._.liftBase
d_liftBase_46 :: T_ClauseBuilder_20 -> () -> AgdaAny -> AgdaAny
d_liftBase_46 v0 = coe d_liftBase_34 (coe v0)
-- Tactic.ClauseBuilder._.toClause
d_toClause_48 :: T_ClauseBuilder_20 -> AgdaAny -> AgdaAny
d_toClause_48 v0 = coe d_toClause_38 (coe v0)
-- Tactic.ClauseBuilder.SinglePattern
d_SinglePattern_50 :: ()
d_SinglePattern_50 = erased
-- Tactic.ClauseBuilder.typedVarSinglePattern
d_typedVarSinglePattern_52 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typedVarSinglePattern_52 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v1)))
             (coe
                MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.Reflection.C_var_252
                   (coe (0 :: Integer))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.varSinglePattern
d_varSinglePattern_60 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_varSinglePattern_60 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v1)
                      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))))
             (coe
                MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.Reflection.C_var_252
                   (coe (0 :: Integer))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.multiSinglePattern
d_multiSinglePattern_66 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_multiSinglePattern_66 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v2 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
                 (coe
                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                    (coe
                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                       (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                          (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                          (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                    (coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))))
         (coe v0))
      (coe v1)
-- Tactic.ClauseBuilder.findIndexDefault
d_findIndexDefault_74 :: [Integer] -> Integer -> Integer -> Integer
d_findIndexDefault_74 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Data.List.Base.du_filter_648
              (coe
                 (\ v3 ->
                    case coe v3 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                        -> coe
                             MAlonzo.Code.Class.DecEq.Core.d__'8799'__16
                             MAlonzo.Code.Class.DecEq.Instances.d_DecEq'45'ℕ_22 v5 v2
                      _ -> MAlonzo.RTE.mazUnreachableError))
              (coe
                 MAlonzo.Code.Data.List.Base.du_zipWith_104
                 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32)
                 (coe
                    MAlonzo.Code.Data.List.Base.du_applyUpTo_360 (coe (\ v3 -> v3))
                    (coe
                       MAlonzo.Code.Data.List.Base.du_foldr_216
                       (let v3 = \ v3 -> addInt (coe (1 :: Integer)) (coe v3) in
                        coe (coe (\ v4 -> v3)))
                       (coe (0 :: Integer)) (coe v0)))
                 (coe v0)) in
    coe
      (case coe v3 of
         [] -> coe v1
         (:) v4 v5
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7 -> coe v6
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Tactic.ClauseBuilder.singlePatternFromPattern
d_singlePatternFromPattern_106 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_singlePatternFromPattern_106 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                MAlonzo.Code.Data.List.Base.du_replicate_278
                (coe
                   MAlonzo.Code.Data.List.Base.du_length_268
                   (d_appearingIndices_116 (coe v1) (coe v2) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                   (coe ("" :: Data.Text.Text))
                   (coe
                      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                      (coe
                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                         (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))))
             (coe
                MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v1)
                (coe d_replacePatternIndex_140 (coe v1) (coe v2) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder._.appearingIndices
d_appearingIndices_116 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_ArgInfo_76 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 -> [Integer]
d_appearingIndices_116 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 v3 v4
        -> coe d_appearingIndicesHelper_118 (coe v0) (coe v1) (coe v4)
      MAlonzo.Code.Agda.Builtin.Reflection.C_dot_248 v3
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Agda.Builtin.Reflection.C_var_252 v3
        -> coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v3)
      MAlonzo.Code.Agda.Builtin.Reflection.C_lit_256 v3
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Agda.Builtin.Reflection.C_proj_260 v3
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      MAlonzo.Code.Agda.Builtin.Reflection.C_absurd_264 v3
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder._.appearingIndicesHelper
d_appearingIndicesHelper_118 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_ArgInfo_76 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] -> [Integer]
d_appearingIndicesHelper_118 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v5 v6
               -> coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe d_appearingIndices_116 (coe v0) (coe v1) (coe v6))
                    (coe d_appearingIndicesHelper_118 (coe v0) (coe v1) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder._.normalisedIndexList
d_normalisedIndexList_138 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_ArgInfo_76 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 -> [Integer]
d_normalisedIndexList_138 v0 v1
  = coe
      MAlonzo.Code.Data.List.Sort.MergeSort.Base.du_sort_166
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'8804''45'decTotalOrder_2882)
      (coe
         MAlonzo.Code.Data.List.Base.du_deduplicate_882
         (coe MAlonzo.Code.Data.Nat.Properties.d__'8799'__2710)
         (coe d_appearingIndices_116 (coe v0) (coe v1) (coe v1)))
-- Tactic.ClauseBuilder._.replacePatternIndex
d_replacePatternIndex_140 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_ArgInfo_76 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158
d_replacePatternIndex_140 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 (coe v3)
             (coe d_replacePatternIndexHelper_142 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Agda.Builtin.Reflection.C_dot_248 v3 -> coe v2
      MAlonzo.Code.Agda.Builtin.Reflection.C_var_252 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_var_252
             (coe
                d_findIndexDefault_74
                (coe d_normalisedIndexList_138 (coe v0) (coe v1))
                (coe (0 :: Integer)) (coe v3))
      MAlonzo.Code.Agda.Builtin.Reflection.C_lit_256 v3 -> coe v2
      MAlonzo.Code.Agda.Builtin.Reflection.C_proj_260 v3 -> coe v2
      MAlonzo.Code.Agda.Builtin.Reflection.C_absurd_264 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder._.replacePatternIndexHelper
d_replacePatternIndexHelper_142 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_ArgInfo_76 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_replacePatternIndexHelper_142 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v5)
                       (coe d_replacePatternIndex_140 (coe v0) (coe v1) (coe v6)))
                    (coe d_replacePatternIndexHelper_142 (coe v0) (coe v1) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder._.ctxSinglePatterns
d_ctxSinglePatterns_180 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny
d_ctxSinglePatterns_180 ~v0 v1 ~v2 v3 ~v4
  = du_ctxSinglePatterns_180 v1 v3
du_ctxSinglePatterns_180 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 -> AgdaAny
du_ctxSinglePatterns_180 v0 v1
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased
      (coe
         MAlonzo.Code.Class.MonadTC.du_getContext_678 (coe v0) (coe v1))
      (\ v2 ->
         coe
           MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
           (coe
              MAlonzo.Code.Data.List.Base.du_map_22
              (coe d_singlePatternFromPattern_106)
              (coe
                 MAlonzo.Code.Meta.Prelude.du_zipWithIndex_34
                 (coe
                    (\ v3 v4 ->
                       case coe v4 of
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                           -> case coe v6 of
                                MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v7 v8
                                  -> coe
                                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v7)
                                       (coe MAlonzo.Code.Agda.Builtin.Reflection.C_var_252 (coe v3))
                                _ -> MAlonzo.RTE.mazUnreachableError
                         _ -> MAlonzo.RTE.mazUnreachableError))
                 (coe v2))))
-- Tactic.ClauseBuilder._.constrToPattern
d_constrToPattern_190 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_constrToPattern_190 ~v0 v1 ~v2 v3 v4 v5 ~v6
  = du_constrToPattern_190 v1 v3 v4 v5
du_constrToPattern_190 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
du_constrToPattern_190 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased
      (coe
         MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
         (MAlonzo.Code.Class.Applicative.Core.d_super_18
            (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
         () erased () erased MAlonzo.Code.Reflection.Utils.Core.d_viewTy_22
         (coe
            MAlonzo.Code.Class.MonadTC.du_runAndReset_182 (coe v0) (coe v2)
            (coe ())
            (coe
               MAlonzo.Code.Class.MonadReader.d_local_40 v1 () erased
               (\ v4 ->
                  coe
                    MAlonzo.Code.Class.MonadTC.C_TCEnv'46'constructor_205
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Class.MonadTC.d_reconstruction_44 (coe v4))
                    (coe MAlonzo.Code.Class.MonadTC.d_noConstraints_46 (coe v4))
                    (coe MAlonzo.Code.Class.MonadTC.d_reduction_48 (coe v4))
                    (coe MAlonzo.Code.Class.MonadTC.d_globalContext_50 (coe v4))
                    (coe MAlonzo.Code.Class.MonadTC.d_localContext_52 (coe v4))
                    (coe MAlonzo.Code.Class.MonadTC.d_goal_54 (coe v4))
                    (coe MAlonzo.Code.Class.MonadTC.d_options_56 (coe v4)))
               (coe
                  MAlonzo.Code.Class.MonadTC.d_inferType_136 v2
                  (coe
                     MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 (coe v3)
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
      (\ v4 ->
         case coe v4 of
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
             -> coe
                  MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                  (coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Data.List.Base.du_map_22
                        (coe
                           (\ v7 ->
                              case coe v7 of
                                MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v8 v9
                                  -> case coe v9 of
                                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v10 v11
                                         -> coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                 (coe v10)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                _ -> MAlonzo.RTE.mazUnreachableError))
                        (coe v5))
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
                           MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 (coe v3)
                           (coe
                              MAlonzo.Code.Data.List.Base.du_zipWith_104
                              (coe
                                 (\ v7 v8 ->
                                    case coe v7 of
                                      MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v9 v10
                                        -> case coe v10 of
                                             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v11 v12
                                               -> coe
                                                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                    (coe v11)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Reflection.C_var_252
                                                       (coe v8))
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError))
                              (coe v5)
                              (coe
                                 MAlonzo.Code.Data.List.Base.d_downFrom_404
                                 (coe MAlonzo.Code.Data.List.Base.du_length_268 v5))))))
           _ -> MAlonzo.RTE.mazUnreachableError)
-- Tactic.ClauseBuilder._.constrToPatternTyped
d_constrToPatternTyped_218 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
d_constrToPatternTyped_218 ~v0 v1 v2 v3 v4 v5 v6
  = du_constrToPatternTyped_218 v1 v2 v3 v4 v5 v6
du_constrToPatternTyped_218 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  AgdaAny ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
du_constrToPatternTyped_218 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased
      (coe
         MAlonzo.Code.Reflection.Utils.TCI.du_applyWithVisibility_476
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5))
      (\ v6 ->
         coe
           MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
           (coe ())
           (coe
              MAlonzo.Code.Class.MonadTC.du_debugLog'7504'_578 (coe v0) (coe v3)
              (coe v2)
              (coe
                 MAlonzo.Code.Class.MonadTC.du__'8759''7496''7504'__540 (coe v0)
                 (coe
                    MAlonzo.Code.Class.MonadTC.du__'7515''8319'_556 (coe v0) (coe v3)
                    (coe v2) (coe ()) (coe v6))
                 (coe
                    MAlonzo.Code.Class.MonadTC.du_IsMErrorPart'45'MErrorPartWrap_532)
                 (coe
                    MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                    (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
           (coe
              MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
              erased
              (coe
                 MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
                 (MAlonzo.Code.Class.Applicative.Core.d_super_18
                    (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
                 () erased () erased MAlonzo.Code.Reflection.Utils.Core.d_viewTy_22
                 (coe
                    MAlonzo.Code.Class.MonadReader.d_local_40 v2 () erased
                    (\ v7 ->
                       coe
                         MAlonzo.Code.Class.MonadTC.C_TCEnv'46'constructor_205
                         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                         (coe MAlonzo.Code.Class.MonadTC.d_reconstruction_44 (coe v7))
                         (coe MAlonzo.Code.Class.MonadTC.d_noConstraints_46 (coe v7))
                         (coe MAlonzo.Code.Class.MonadTC.d_reduction_48 (coe v7))
                         (coe MAlonzo.Code.Class.MonadTC.d_globalContext_50 (coe v7))
                         (coe MAlonzo.Code.Class.MonadTC.d_localContext_52 (coe v7))
                         (coe MAlonzo.Code.Class.MonadTC.d_goal_54 (coe v7))
                         (coe MAlonzo.Code.Class.MonadTC.d_options_56 (coe v7)))
                    (coe MAlonzo.Code.Class.MonadTC.d_inferType_136 v3 v6)))
              (\ v7 ->
                 case coe v7 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                     -> coe
                          MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                             (coe
                                MAlonzo.Code.Data.List.Base.du_map_22
                                (coe
                                   (\ v10 ->
                                      case coe v10 of
                                        MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v11 v12
                                          -> coe
                                               seq (coe v12)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v11) (coe v12))
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                (coe v8))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                   (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                   (coe
                                      MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 (coe v4)
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du_zipWith_104
                                      (coe
                                         (\ v10 v11 ->
                                            case coe v10 of
                                              MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v12 v13
                                                -> case coe v13 of
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v14 v15
                                                       -> coe
                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                            (coe v14)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Reflection.C_var_252
                                                               (coe v11))
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                      (coe v8)
                                      (coe
                                         MAlonzo.Code.Data.List.Base.d_downFrom_404
                                         (coe MAlonzo.Code.Data.List.Base.du_length_268 v8))))))
                   _ -> MAlonzo.RTE.mazUnreachableError)))
-- Tactic.ClauseBuilder._.constructorPatterns
d_constructorPatterns_248 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 -> AgdaAny
d_constructorPatterns_248 ~v0 v1 v2 ~v3 v4 v5
  = du_constructorPatterns_248 v1 v2 v4 v5
du_constructorPatterns_248 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 -> AgdaAny
du_constructorPatterns_248 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v4 v5
        -> coe
             MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
             erased
             (coe
                MAlonzo.Code.Class.MonadTC.du_getConstrsForType_796 (coe v0)
                (coe v1) (coe v2) (coe v5))
             (\ v6 ->
                coe
                  MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                  (coe
                     MAlonzo.Code.Class.Functor.Core.du__'60''38''62'__30
                     (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
                     (coe ()) (coe ()) (coe v6)
                     (coe
                        (\ v7 ->
                           case coe v7 of
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                               -> coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Data.List.Base.du_map_22
                                       (coe
                                          (\ v10 ->
                                             case coe v10 of
                                               MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v11 v12
                                                 -> coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v11) (coe v12)
                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             MAlonzo.Code.Reflection.Utils.Core.d_viewTy_22
                                             (coe v9))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 (coe v4)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 (coe v8)
                                          (coe
                                             MAlonzo.Code.Meta.Prelude.du_zipWithIndex_34
                                             (coe
                                                (\ v10 v11 ->
                                                   case coe v11 of
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v12 v13
                                                       -> case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v14 v15
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                                   (coe v14)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Reflection.C_var_252
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                         (coe
                                                                            MAlonzo.Code.Data.List.Base.du_length_268
                                                                            (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                                               (coe
                                                                                  MAlonzo.Code.Reflection.Utils.Core.d_viewTy_22
                                                                                  (coe v9))))
                                                                         (addInt
                                                                            (coe (1 :: Integer))
                                                                            (coe v10))))
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Reflection.Utils.Core.d_viewTy_22
                                                   (coe v9))))))
                             _ -> MAlonzo.RTE.mazUnreachableError))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder._.constructorPatterns'
d_constructorPatterns''_276 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_constructorPatterns''_276 ~v0 v1 v2 v3 v4 v5
  = du_constructorPatterns''_276 v1 v2 v3 v4 v5
du_constructorPatterns''_276 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_constructorPatterns''_276 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased
      (coe
         MAlonzo.Code.Class.MonadTC.du_getConstrsForType_796 (coe v0)
         (coe v1) (coe v3) (coe v4))
      (coe
         MAlonzo.Code.Class.Traversable.Core.du_traverse_44
         (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
         (coe
            MAlonzo.Code.Class.Traversable.Instances.d_TraversableM'45'List_28)
         (coe ()) (coe ()) (coe v0)
         (coe
            (\ v5 ->
               coe
                 du_constrToPattern_190 (coe v0) (coe v2) (coe v3)
                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))))
-- Tactic.ClauseBuilder._.constructorPatternsTyped
d_constructorPatternsTyped_286 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
d_constructorPatternsTyped_286 ~v0 v1 v2 v3 v4 v5 v6
  = du_constructorPatternsTyped_286 v1 v2 v3 v4 v5 v6
du_constructorPatternsTyped_286 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] -> AgdaAny
du_constructorPatternsTyped_286 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased
      (coe
         MAlonzo.Code.Class.MonadTC.du_getConstrsForType_796 (coe v0)
         (coe v1) (coe v3) (coe v4))
      (coe
         MAlonzo.Code.Class.Traversable.Core.du_traverse_44
         (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
         (coe
            MAlonzo.Code.Class.Traversable.Instances.d_TraversableM'45'List_28)
         (coe ()) (coe ()) (coe v0)
         (coe
            (\ v6 ->
               coe
                 du_constrToPatternTyped_218 (coe v0) (coe v1) (coe v2) (coe v3)
                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)) (coe v5))))
-- Tactic.ClauseBuilder.ClauseInfo
d_ClauseInfo_298 :: ()
d_ClauseInfo_298 = erased
-- Tactic.ClauseBuilder.ClauseExpr
d_ClauseExpr_300 = ()
newtype T_ClauseExpr_300
  = C_MatchExpr_302 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Tactic.ClauseBuilder.multiClauseExpr
d_multiClauseExpr_304 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_ClauseExpr_300
d_multiClauseExpr_304 v0
  = coe
      C_MatchExpr_302
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22 (coe d_helper_320) (coe v0))
-- Tactic.ClauseBuilder._.helper'
d_helper''_310 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_helper''_310 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             [] -> coe v2
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe
                       C_MatchExpr_302
                       (coe
                          MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                             (coe
                                d_helper''_310
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                   (coe v2))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder._.helper
d_helper_320 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_helper_320 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Data.List.NonEmpty.Base.C__'8759'__34 v3 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                    (coe
                       d_helper''_310
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.clauseExprToClauseInfo
d_clauseExprToClauseInfo_328 ::
  T_ClauseExpr_300 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_clauseExprToClauseInfo_328 v0
  = case coe v0 of
      C_MatchExpr_302 v1
        -> case coe v1 of
             [] -> coe v1
             (:) v2 v3
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                      -> case coe v5 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v6
                             -> coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du_map_22
                                     (coe
                                        MAlonzo.Code.Data.Product.Base.du_map'8321'_138
                                        (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)))
                                     (coe d_clauseExprToClauseInfo_328 (coe v6)))
                                  (coe d_clauseExprToClauseInfo_328 (coe C_MatchExpr_302 (coe v3)))
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v6
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v4))
                                     (coe v6))
                                  (coe d_clauseExprToClauseInfo_328 (coe C_MatchExpr_302 (coe v3)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.clauseInfoToClauseArgs
d_clauseInfoToClauseArgs_344 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_clauseInfoToClauseArgs_344 v0
  = let v1 = coe du_helper_352 (coe (0 :: Integer)) (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Tactic.ClauseBuilder._.helper
d_helper_352 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_helper_352 ~v0 v1 v2 = du_helper_352 v1 v2
du_helper_352 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_helper_352 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v0))
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v6 v7
                      -> let v8 = coe du_helper_352 (coe v0) (coe v3) in
                         coe
                           (case coe v8 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                -> case coe v10 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                                               (coe v9))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                     (coe v6)
                                                     (coe
                                                        MAlonzo.Code.Reflection.Utils.Substitute.d_mapVariables_272
                                                        (coe (\ v13 -> addInt (coe v12) (coe v13)))
                                                        (coe v7)))
                                                  (coe v11))
                                               (coe
                                                  addInt
                                                  (coe MAlonzo.Code.Data.List.Base.du_length_268 v4)
                                                  (coe v12)))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.clauseInfoToClause
d_clauseInfoToClause_394 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160
d_clauseInfoToClause_394 v0 v1
  = let v2
          = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe du_helper_352 (coe (0 :: Integer)) (coe v0)) in
    coe
      (let v3
             = MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (coe du_helper_352 (coe (0 :: Integer)) (coe v0))) in
       coe
         (case coe v1 of
            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
              -> coe
                   MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272 (coe v2) (coe v3)
                   (coe v4)
            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
              -> coe
                   MAlonzo.Code.Agda.Builtin.Reflection.C_absurd'45'clause_278
                   (coe v2) (coe v3)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Tactic.ClauseBuilder.clauseExprToClauses
d_clauseExprToClauses_422 ::
  T_ClauseExpr_300 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160]
d_clauseExprToClauses_422 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe
         (\ v1 ->
            case coe v1 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
                -> coe d_clauseInfoToClause_394 (coe v2) (coe v3)
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe d_clauseExprToClauseInfo_328 (coe v0))
-- Tactic.ClauseBuilder.nonBindingClause
d_nonBindingClause_432 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160
d_nonBindingClause_432
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Tactic.ClauseBuilder.clauseExprToPatLam
d_clauseExprToPatLam_434 ::
  T_ClauseExpr_300 -> MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_clauseExprToPatLam_434 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196
      (coe d_clauseExprToClauses_422 (coe v0))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Tactic.ClauseBuilder.ContextMonad
d_ContextMonad_444 a0 a1 = ()
newtype T_ContextMonad_444
  = C_ContextMonad'46'constructor_50587 (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                         () ->
                                         MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
                                         AgdaAny -> AgdaAny)
-- Tactic.ClauseBuilder.ContextMonad.introPatternM
d_introPatternM_452 ::
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
d_introPatternM_452 v0
  = case coe v0 of
      C_ContextMonad'46'constructor_50587 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.ContextMonad.extendContextM
d_extendContextM_454 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 -> AgdaAny -> AgdaAny
d_extendContextM_454 ~v0 ~v1 v2 v3 ~v4 v5 v6
  = du_extendContextM_454 v2 v3 v5 v6
du_extendContextM_454 ::
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 -> AgdaAny -> AgdaAny
du_extendContextM_454 v0 v1 v2 v3
  = coe
      d_introPatternM_452 v0 v1 erased
      (d_typedVarSinglePattern_52 (coe ("" :: Data.Text.Text)) (coe v2))
      v3
-- Tactic.ClauseBuilder._.introPatternM
d_introPatternM_464 ::
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
d_introPatternM_464 v0 = coe d_introPatternM_452 (coe v0)
-- Tactic.ClauseBuilder._.ContextMonad-Id
d_ContextMonad'45'Id_470 :: T_ContextMonad_444
d_ContextMonad'45'Id_470
  = coe
      C_ContextMonad'46'constructor_50587 (coe (\ v0 v1 v2 v3 -> v3))
-- Tactic.ClauseBuilder._.refineWithSingle
d_refineWithSingle_490 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  (MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
   MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154) ->
  AgdaAny -> AgdaAny
d_refineWithSingle_490 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_refineWithSingle_490 v1 v3 v4 v5 v6
du_refineWithSingle_490 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  (MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
   MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154) ->
  AgdaAny -> AgdaAny
du_refineWithSingle_490 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased
      (coe
         MAlonzo.Code.Class.MonadTC.du_goalTy_744 (coe v0) (coe v2)
         (coe v1))
      (\ v5 ->
         coe
           MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
           erased
           (coe
              MAlonzo.Code.Class.MonadTC.du_newMeta_392 v2
              (coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))
           (\ v6 ->
              coe
                MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                erased
                (coe MAlonzo.Code.Class.MonadTC.d_checkType_138 v2 (coe v3 v6) v5)
                (\ v7 ->
                   coe
                     MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                     erased
                     (coe MAlonzo.Code.Class.MonadTC.du_runWithHole_824 v1 () v6 v4)
                     (\ v8 ->
                        coe
                          MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                          (coe ()) (coe MAlonzo.Code.Class.MonadTC.d_unify_132 v2 v6 v8)
                          (coe
                             MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                             (coe v3 v8))))))
-- Tactic.ClauseBuilder._.caseMatch
d_caseMatch_504 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  AgdaAny -> AgdaAny
d_caseMatch_504 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_caseMatch_504 v1 v3 v4 v5 v6
du_caseMatch_504 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  AgdaAny -> AgdaAny
du_caseMatch_504 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
      (coe ())
      (coe
         MAlonzo.Code.Class.MonadTC.du_debugLog_570 (coe v0) (coe v2)
         (coe v1)
         (coe
            MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
            (coe ("Match" :: Data.Text.Text))
            (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
            (coe
               MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v3)
               (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
      (coe
         du_refineWithSingle_490 (coe v0) (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Reflection.QQuotedDefinitions.d_'96'case_of__20
            (coe v3))
         (coe
            MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
            (MAlonzo.Code.Class.Applicative.Core.d_super_18
               (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
            () erased () erased
            (\ v5 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196
                 (coe d_clauseExprToClauses_422 (coe v5))
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
            v4))
-- Tactic.ClauseBuilder._.currentTyConstrPatterns
d_currentTyConstrPatterns_512 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny
d_currentTyConstrPatterns_512 ~v0 v1 v2 v3 v4
  = du_currentTyConstrPatterns_512 v1 v2 v3 v4
du_currentTyConstrPatterns_512 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny
du_currentTyConstrPatterns_512 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased
      (coe
         MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
         (MAlonzo.Code.Class.Applicative.Core.d_super_18
            (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
         () erased () erased
         MAlonzo.Code.Reflection.Utils.Core.d_viewTy'8242'_58
         (coe
            MAlonzo.Code.Class.MonadTC.du_goalTy_744 (coe v0) (coe v3)
            (coe v2)))
      (\ v4 ->
         case coe v4 of
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
             -> let v7
                      = coe
                          MAlonzo.Code.Class.MonadTC.du_error1_724 (coe v1) (coe ())
                          (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                          (coe
                             ("currentTyConstrPatterns: Goal type is not a forall!"
                              ::
                              Data.Text.Text)) in
                coe
                  (case coe v5 of
                     (:) v8 v9
                       -> coe
                            du_constructorPatterns''_276 (coe v0) (coe v1) (coe v2) (coe v3)
                            (coe MAlonzo.Code.Reflection.AST.Argument.du_unArg_74 (coe v8))
                     _ -> coe v7)
           _ -> MAlonzo.RTE.mazUnreachableError)
-- Tactic.ClauseBuilder.stripMetaLambdas
d_stripMetaLambdas_518 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_stripMetaLambdas_518 = coe d_helper_524 (coe (0 :: Integer))
-- Tactic.ClauseBuilder._.helper
d_helper_524 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_helper_524 v0 v1
  = let v2
          = coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216 in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_lam_190 v3 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v5 v6
                  -> coe
                       d_helper_524 (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v6)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v3 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 (coe v3)
                (coe
                   MAlonzo.Code.Reflection.AST.Argument.du_map'45'Args_62
                   (coe
                      MAlonzo.Code.Reflection.Utils.Substitute.d_mapVars_246
                      (coe
                         (\ v5 -> coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v5 v0)))
                   (coe
                      MAlonzo.Code.Data.List.Base.du_take_530
                      (coe
                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                         (coe MAlonzo.Code.Data.List.Base.du_length_268 v4) v0)
                      (coe v4)))
         _ -> coe v2)
-- Tactic.ClauseBuilder._.isProj
d_isProj_554 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 -> Bool
d_isProj_554 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_isProj_554 v5
du_isProj_554 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 -> Bool
du_isProj_554 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_proj_260 v2
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
         _ -> coe v1)
-- Tactic.ClauseBuilder._.specializeType
d_specializeType_556 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
d_specializeType_556 ~v0 v1 v2 v3 v4 v5 v6
  = du_specializeType_556 v1 v2 v3 v4 v5 v6
du_specializeType_556 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 -> AgdaAny
du_specializeType_556 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> case coe v7 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v8 v9
               -> coe
                    MAlonzo.Code.Reflection.Utils.TCI.du_inDebugPath_318 (coe v0)
                    (coe v2) (coe v3) (coe ())
                    (coe ("specializeType" :: Data.Text.Text))
                    (coe
                       MAlonzo.Code.Class.MonadTC.du_runAndReset_182 (coe v0) (coe v3)
                       (coe ())
                       (coe
                          MAlonzo.Code.Class.Monad.Core.du__'62''62'__24 (coe v0) (coe ())
                          (coe ())
                          (coe
                             MAlonzo.Code.Class.MonadTC.du_debugLog_570 (coe v0) (coe v3)
                             (coe v2)
                             (coe
                                MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                (coe ("Goal type to specialize: " :: Data.Text.Text))
                                (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                (coe
                                   MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36 (coe v5)
                                   (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                          (coe
                             MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
                             erased
                             (coe
                                MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased
                                (d_clauseExprToClauses_422
                                   (coe
                                      C_MatchExpr_302
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                            (coe
                                               MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))))
                                         (coe
                                            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                            (coe du_isProj_554 (coe v9))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                            (coe
                                               MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     d_varSinglePattern_60
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                                        (coe v8) (coe ("_" :: Data.Text.Text))))
                                                  (coe
                                                     MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))))))))))
                             (\ v10 ->
                                let v11
                                      = coe
                                          MAlonzo.Code.Class.MonadTC.du_error1_724 (coe v1) (coe ())
                                          (coe
                                             MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                          (coe ("BUG" :: Data.Text.Text)) in
                                coe
                                  (case coe v10 of
                                     (:) v12 v13
                                       -> case coe v12 of
                                            MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272 v14 v15 v16
                                              -> coe
                                                   MAlonzo.Code.Class.Monad.Core.du__'62''62'__24
                                                   (coe v0) (coe ()) (coe ())
                                                   (coe
                                                      MAlonzo.Code.Class.MonadTC.du_debugLog_570
                                                      (coe v0) (coe v3) (coe v2)
                                                      (coe
                                                         MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                                         (coe ("With pattern: " :: Data.Text.Text))
                                                         (coe
                                                            MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                                         (coe
                                                            MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                                            (coe v10)
                                                            (coe
                                                               MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'ListClause_30)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
                                                   (coe
                                                      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22
                                                      v0 () erased () erased
                                                      (coe
                                                         MAlonzo.Code.Class.MonadTC.d_checkType_138
                                                         v3
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196
                                                            (coe v10)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                         v5)
                                                      (\ v17 ->
                                                         let v18
                                                               = coe
                                                                   MAlonzo.Code.Class.Monad.Core.du__'62''62'__24
                                                                   (coe v0) (coe ()) (coe ())
                                                                   (coe
                                                                      MAlonzo.Code.Class.MonadTC.du_debugLog_570
                                                                      (coe v0) (coe v3) (coe v2)
                                                                      (coe
                                                                         MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                                                         (coe
                                                                            ("BUG in specializeType:"
                                                                             ::
                                                                             Data.Text.Text))
                                                                         (coe
                                                                            MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                                                         (coe
                                                                            MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                                                            (coe v17)
                                                                            (coe
                                                                               MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                                                                            (coe
                                                                               MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                                                               (coe
                                                                                  ("\nWith pattern:"
                                                                                   ::
                                                                                   Data.Text.Text))
                                                                               (coe
                                                                                  MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                                                               (coe
                                                                                  MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                                                                  (coe v10)
                                                                                  (coe
                                                                                     MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'ListClause_30)
                                                                                  (coe
                                                                                     MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                                                                     (coe
                                                                                        ("\nWith type:"
                                                                                         ::
                                                                                         Data.Text.Text))
                                                                                     (coe
                                                                                        MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                                                                     (coe
                                                                                        MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                                                                        (coe v5)
                                                                                        (coe
                                                                                           MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'Term_20)
                                                                                        (coe
                                                                                           MAlonzo.Code.Reflection.Debug.du__'8759''7496'__36
                                                                                           (coe
                                                                                              ("\nSinglePattern:"
                                                                                               ::
                                                                                               Data.Text.Text))
                                                                                           (coe
                                                                                              MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))))))
                                                                   (coe
                                                                      MAlonzo.Code.Class.MonadTC.du_error1_724
                                                                      (coe v1) (coe ())
                                                                      (coe
                                                                         MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                                                      (coe
                                                                         ("BUG"
                                                                          ::
                                                                          Data.Text.Text))) in
                                                         coe
                                                           (case coe v17 of
                                                              MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196 v19 v20
                                                                -> case coe v19 of
                                                                     (:) v21 v22
                                                                       -> case coe v21 of
                                                                            MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272 v23 v24 v25
                                                                              -> case coe v25 of
                                                                                   MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v26 v27
                                                                                     -> case coe
                                                                                               v20 of
                                                                                          []
                                                                                            -> coe
                                                                                                 MAlonzo.Code.Class.Monad.Core.du__'62''62'__24
                                                                                                 (coe
                                                                                                    v0)
                                                                                                 (coe
                                                                                                    ())
                                                                                                 (coe
                                                                                                    ())
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Class.MonadTC.du_debugLog1_728
                                                                                                    (coe
                                                                                                       v0)
                                                                                                    (coe
                                                                                                       v3)
                                                                                                    (coe
                                                                                                       v2)
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                                                                                                    (coe
                                                                                                       ("New context:"
                                                                                                        ::
                                                                                                        Data.Text.Text)))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Class.Monad.Core.du__'62''62'__24
                                                                                                    (coe
                                                                                                       v0)
                                                                                                    (coe
                                                                                                       ())
                                                                                                    (coe
                                                                                                       ())
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Reflection.Utils.TCI.du_logContext_286
                                                                                                       (coe
                                                                                                          v0)
                                                                                                       (coe
                                                                                                          v1)
                                                                                                       (coe
                                                                                                          v2)
                                                                                                       (coe
                                                                                                          v3)
                                                                                                       (coe
                                                                                                          v23))
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22
                                                                                                       v0
                                                                                                       ()
                                                                                                       erased
                                                                                                       ()
                                                                                                       erased
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Class.MonadTC.du_extendContext''_702
                                                                                                          (coe
                                                                                                             v2)
                                                                                                          (coe
                                                                                                             ())
                                                                                                          (coe
                                                                                                             v23)
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Class.MonadTC.d_inferType_136
                                                                                                             v3
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214
                                                                                                                (coe
                                                                                                                   v26)
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Reflection.AST.Argument.du_map'45'Args_62
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Reflection.Utils.Substitute.d_mapVars_246
                                                                                                                      (coe
                                                                                                                         (\ v28 ->
                                                                                                                            coe
                                                                                                                              MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                                                                              v28
                                                                                                                              (0 ::
                                                                                                                                 Integer))))
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Data.List.Base.du_take_530
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Data.List.Base.du_length_268
                                                                                                                            v27)
                                                                                                                         (0 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         v27))))))
                                                                                                       (\ v28 ->
                                                                                                          coe
                                                                                                            MAlonzo.Code.Class.Monad.Core.d_return_20
                                                                                                            v0
                                                                                                            ()
                                                                                                            erased
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                               (coe
                                                                                                                  v28)
                                                                                                               (coe
                                                                                                                  v23)))))
                                                                                          _ -> coe
                                                                                                 v18
                                                                                   _ -> coe v18
                                                                            _ -> coe v18
                                                                     _ -> coe v18
                                                              _ -> coe v18)))
                                            _ -> coe v11
                                     _ -> coe v11)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder._.ContextMonad-MonadTC
d_ContextMonad'45'MonadTC_596 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> T_ContextMonad_444
d_ContextMonad'45'MonadTC_596 ~v0 v1 v2 v3 v4
  = du_ContextMonad'45'MonadTC_596 v1 v2 v3 v4
du_ContextMonad'45'MonadTC_596 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> T_ContextMonad_444
du_ContextMonad'45'MonadTC_596 v0 v1 v2 v3
  = coe
      C_ContextMonad'46'constructor_50587
      (coe
         (\ v4 v5 v6 ->
            case coe v6 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                -> coe
                     seq (coe v8)
                     (coe
                        (\ v9 ->
                           coe
                             MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased v4
                             erased
                             (coe
                                MAlonzo.Code.Class.MonadTC.du_goalTy_744 (coe v0) (coe v3)
                                (coe v2))
                             (\ v10 ->
                                coe
                                  MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased v4
                                  erased
                                  (coe
                                     du_specializeType_556 (coe v0) (coe v1) (coe v2) (coe v3)
                                     (coe v6) (coe v10))
                                  (\ v11 ->
                                     case coe v11 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                         -> coe
                                              MAlonzo.Code.Class.MonadTC.du_extendContext''_702
                                              (coe v2) (coe v4) (coe v13)
                                              (coe
                                                 MAlonzo.Code.Class.MonadTC.du_runWithGoalTy_830 v2
                                                 v4 v12 v9)
                                       _ -> MAlonzo.RTE.mazUnreachableError))))
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Tactic.ClauseBuilder.ClauseExprM.matchExprM
d_matchExprM_622 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_matchExprM_622 ~v0 v1 v2 v3 = du_matchExprM_622 v1 v2 v3
du_matchExprM_622 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_matchExprM_622 v0 v1 v2
  = coe
      MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
      (MAlonzo.Code.Class.Applicative.Core.d_super_18
         (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
      () erased () erased (coe C_MatchExpr_302)
      (coe
         MAlonzo.Code.Class.Traversable.Core.du_traverse_44
         (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
         (coe
            MAlonzo.Code.Class.Traversable.Instances.d_TraversableM'45'List_28)
         (coe ()) (coe ()) (coe v0)
         (coe
            (\ v3 ->
               coe
                 MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
                 (MAlonzo.Code.Class.Applicative.Core.d_super_18
                    (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
                 () erased () erased
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)) (coe v4))
                 (coe
                    d_introPatternM_452 v1 () erased
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))))
         (coe v2))
-- Tactic.ClauseBuilder.ClauseExprM.multiMatchExprM
d_multiMatchExprM_632 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
d_multiMatchExprM_632 ~v0 v1 v2 v3
  = du_multiMatchExprM_632 v1 v2 v3
du_multiMatchExprM_632 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny
du_multiMatchExprM_632 v0 v1 v2
  = coe
      du_matchExprM_622 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe du_helper_648 (coe v0) (coe v1)) (coe v2))
-- Tactic.ClauseBuilder.ClauseExprM._.helper'
d_helper''_638 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_helper''_638 ~v0 v1 v2 v3 = du_helper''_638 v1 v2 v3
du_helper''_638 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
du_helper''_638 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             [] -> coe v4
             (:) v5 v6
               -> coe
                    MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
                    (MAlonzo.Code.Class.Applicative.Core.d_super_18
                       (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
                    () erased () erased (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                    (coe
                       du_matchExprM_622 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                             (coe
                                du_helper''_638 (coe v0) (coe v1)
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                   (coe v4))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.ClauseExprM._.helper
d_helper_648 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_helper_648 ~v0 v1 v2 v3 = du_helper_648 v1 v2 v3
du_helper_648 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_helper_648 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Data.List.NonEmpty.Base.C__'8759'__34 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                    (coe
                       du_helper''_638 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6) (coe v4)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.ClauseExprM.singleMatchExpr
d_singleMatchExpr_656 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
d_singleMatchExpr_656 ~v0 v1 v2 v3 v4
  = du_singleMatchExpr_656 v1 v2 v3 v4
du_singleMatchExpr_656 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
du_singleMatchExpr_656 v0 v1 v2 v3
  = coe
      du_matchExprM_622 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)))
-- Tactic.ClauseBuilder.ClauseExprM.singleTelescopeMatchExpr
d_singleTelescopeMatchExpr_662 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22 ->
  AgdaAny -> AgdaAny
d_singleTelescopeMatchExpr_662 ~v0 v1 v2 v3 v4
  = du_singleTelescopeMatchExpr_662 v1 v2 v3 v4
du_singleTelescopeMatchExpr_662 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22 ->
  AgdaAny -> AgdaAny
du_singleTelescopeMatchExpr_662 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.List.NonEmpty.Base.C__'8759'__34 v4 v5
        -> coe du_helper_674 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.ClauseExprM._.helper
d_helper_674 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
d_helper_674 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_helper_674 v1 v2 v6 v7 v8
du_helper_674 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> AgdaAny -> AgdaAny
du_helper_674 v0 v1 v2 v3 v4
  = case coe v3 of
      []
        -> coe du_singleMatchExpr_656 (coe v0) (coe v1) (coe v2) (coe v4)
      (:) v5 v6
        -> coe
             du_singleMatchExpr_656 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
                (MAlonzo.Code.Class.Applicative.Core.d_super_18
                   (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
                () erased () erased (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                (coe du_helper_674 (coe v0) (coe v1) (coe v5) (coe v6) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.ClauseExprM.introExpr
d_introExpr_688 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 -> AgdaAny -> AgdaAny
d_introExpr_688 ~v0 v1 v2 v3 v4 = du_introExpr_688 v1 v2 v3 v4
du_introExpr_688 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 -> AgdaAny -> AgdaAny
du_introExpr_688 v0 v1 v2 v3
  = coe
      du_singleMatchExpr_656 (coe v0) (coe v1)
      (coe d_varSinglePattern_60 (coe v2)) (coe v3)
-- Tactic.ClauseBuilder.ClauseExprM.introsExpr
d_introsExpr_694 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22 ->
  AgdaAny -> AgdaAny
d_introsExpr_694 ~v0 v1 v2 v3 v4 = du_introsExpr_694 v1 v2 v3 v4
du_introsExpr_694 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22 ->
  AgdaAny -> AgdaAny
du_introsExpr_694 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.List.NonEmpty.Base.C__'8759'__34 v4 v5
        -> coe du_helper_706 (coe v0) (coe v1) (coe v4) (coe v5) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.ClauseExprM._.helper
d_helper_706 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  AgdaAny -> AgdaAny
d_helper_706 ~v0 v1 v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_helper_706 v1 v2 v6 v7 v8
du_helper_706 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  AgdaAny -> AgdaAny
du_helper_706 v0 v1 v2 v3 v4
  = case coe v3 of
      [] -> coe du_introExpr_688 (coe v0) (coe v1) (coe v2) (coe v4)
      (:) v5 v6
        -> coe
             du_introExpr_688 (coe v0) (coe v1) (coe v2)
             (coe
                MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
                (MAlonzo.Code.Class.Applicative.Core.d_super_18
                   (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
                () erased () erased (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                (coe du_helper_706 (coe v0) (coe v1) (coe v2) (coe v6) (coe v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.ClauseExprM.contMatch
d_contMatch_720 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 -> AgdaAny -> AgdaAny
d_contMatch_720 v0 ~v1 v2 = du_contMatch_720 v0 v2
du_contMatch_720 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 -> AgdaAny -> AgdaAny
du_contMatch_720 v0 v1
  = coe
      MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
      (MAlonzo.Code.Class.Applicative.Core.d_super_18
         (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
      () erased () erased (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
      v1
-- Tactic.ClauseBuilder.ClauseExprM.finishMatch
d_finishMatch_724 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 -> AgdaAny -> AgdaAny
d_finishMatch_724 v0 ~v1 v2 = du_finishMatch_724 v0 v2
du_finishMatch_724 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 -> AgdaAny -> AgdaAny
du_finishMatch_724 v0 v1
  = coe
      MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
      (MAlonzo.Code.Class.Applicative.Core.d_super_18
         (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
      () erased () erased
      (\ v2 ->
         coe
           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
           (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)))
      v1
-- Tactic.ClauseBuilder.ClauseExprM.bindCtxMatchExpr
d_bindCtxMatchExpr_734 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 -> AgdaAny -> AgdaAny
d_bindCtxMatchExpr_734 ~v0 v1 v2 ~v3 v4 ~v5 v6
  = du_bindCtxMatchExpr_734 v1 v2 v4 v6
du_bindCtxMatchExpr_734 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_ContextMonad_444 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  AgdaAny -> AgdaAny
du_bindCtxMatchExpr_734 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 () erased ()
      erased (coe du_ctxSinglePatterns_180 (coe v0) (coe v2))
      (\ v4 ->
         let v5
               = coe
                   MAlonzo.Code.Data.List.NonEmpty.Base.du_fromList_66 (coe v4) in
         coe
           (case coe v5 of
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                -> coe
                     du_singleTelescopeMatchExpr_662 (coe v0) (coe v1) (coe v6)
                     (coe
                        MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
                        (MAlonzo.Code.Class.Applicative.Core.d_super_18
                           (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
                        () erased () erased (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
                        v3)
              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v3
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Tactic.ClauseBuilder.clauseTelescope
d_clauseTelescope_744 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_clauseTelescope_744 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272 v1 v2 v3
        -> coe v1
      MAlonzo.Code.Agda.Builtin.Reflection.C_absurd'45'clause_278 v1 v2
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder._._.bindCtxMatchExpr
d_bindCtxMatchExpr_756 ::
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Class.MonadTC.T_MonadTC_80 ->
  T_ClauseExpr_300 -> T_ClauseExpr_300
d_bindCtxMatchExpr_756 v0 v1 v2 v3
  = coe
      du_bindCtxMatchExpr_734
      (coe MAlonzo.Code.Class.Monad.Id.d_Monad'45'Id_12)
      (coe d_ContextMonad'45'Id_470) v1 v3
-- Tactic.ClauseBuilder._._.contMatch
d_contMatch_758 ::
  T_ClauseExpr_300 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_contMatch_758 v0
  = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v0)
-- Tactic.ClauseBuilder._._.finishMatch
d_finishMatch_760 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_finishMatch_760 v0
  = coe
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0))
-- Tactic.ClauseBuilder._._.introExpr
d_introExpr_762 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_ClauseExpr_300
d_introExpr_762
  = coe
      du_introExpr_688 (coe MAlonzo.Code.Class.Monad.Id.d_Monad'45'Id_12)
      (coe d_ContextMonad'45'Id_470)
-- Tactic.ClauseBuilder._._.introsExpr
d_introsExpr_764 ::
  MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_ClauseExpr_300
d_introsExpr_764
  = coe
      du_introsExpr_694
      (coe MAlonzo.Code.Class.Monad.Id.d_Monad'45'Id_12)
      (coe d_ContextMonad'45'Id_470)
-- Tactic.ClauseBuilder._._.matchExprM
d_matchExprM_766 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_ClauseExpr_300
d_matchExprM_766
  = coe
      du_matchExprM_622
      (coe MAlonzo.Code.Class.Monad.Id.d_Monad'45'Id_12)
      (coe d_ContextMonad'45'Id_470)
-- Tactic.ClauseBuilder._._.multiMatchExprM
d_multiMatchExprM_768 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_ClauseExpr_300
d_multiMatchExprM_768
  = coe
      du_multiMatchExprM_632
      (coe MAlonzo.Code.Class.Monad.Id.d_Monad'45'Id_12)
      (coe d_ContextMonad'45'Id_470)
-- Tactic.ClauseBuilder._._.singleMatchExpr
d_singleMatchExpr_770 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_ClauseExpr_300
d_singleMatchExpr_770
  = coe
      du_singleMatchExpr_656
      (coe MAlonzo.Code.Class.Monad.Id.d_Monad'45'Id_12)
      (coe d_ContextMonad'45'Id_470)
-- Tactic.ClauseBuilder._._.singleTelescopeMatchExpr
d_singleTelescopeMatchExpr_772 ::
  MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_ClauseExpr_300
d_singleTelescopeMatchExpr_772
  = coe
      du_singleTelescopeMatchExpr_662
      (coe MAlonzo.Code.Class.Monad.Id.d_Monad'45'Id_12)
      (coe d_ContextMonad'45'Id_470)
-- Tactic.ClauseBuilder._.instanciatePattern
d_instanciatePattern_774 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_instanciatePattern_774 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe (\ v1 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1)))
      (coe
         d_clauseTelescope_744
         (coe
            MAlonzo.Code.Data.Maybe.Base.d_from'45'just_60
            (coe
               MAlonzo.Code.Data.List.Base.du_head_516
               (coe
                  d_clauseExprToClauses_422
                  (coe
                     du_singleMatchExpr_656
                     (coe MAlonzo.Code.Class.Monad.Id.d_Monad'45'Id_12)
                     (coe d_ContextMonad'45'Id_470) (coe v0)
                     (coe
                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                        (coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))))))))
-- Tactic.ClauseBuilder._.instanciatePatterns
d_instanciatePatterns_778 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160]
d_instanciatePatterns_778 v0 v1
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
             (coe
                MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272 (coe v0) (coe v0)
                (coe v1))
      (:) v2 v3
        -> coe
             d_clauseExprToClauses_422
             (coe
                du_singleTelescopeMatchExpr_662
                (coe MAlonzo.Code.Class.Monad.Id.d_Monad'45'Id_12)
                (coe d_ContextMonad'45'Id_470)
                (coe
                   MAlonzo.Code.Data.List.NonEmpty.Base.C__'8759'__34 (coe v2)
                   (coe v3))
                (coe
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                   (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Tactic.ClauseBuilder.ctxBindingClause
d_ctxBindingClause_788 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Class.MonadTC.T_TCEnv_24 -> AgdaAny
d_ctxBindingClause_788 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
      erased
      (coe
         du_ctxSinglePatterns_180
         (coe
            MAlonzo.Code.Class.MonadReader.du_Monad'45'ReaderT_106
            (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6))
         (coe
            MAlonzo.Code.Class.MonadReader.du_MonadReader'45'ReaderT_120
            (coe MAlonzo.Code.Class.Monad.Instances.d_Monad'45'TC_6))
         v1)
      (\ v2 ->
         coe
           MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
           erased
           (coe
              MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326 () erased
              (d_instanciatePatterns_778
                 (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v2) (coe v0)))
           (\ v3 ->
              let v4
                    = coe
                        MAlonzo.Code.Class.MonadTC.du_error1_724
                        (coe MAlonzo.Code.Meta.Init.d_iMonadError'45'TC_10) (coe ())
                        (coe MAlonzo.Code.Reflection.Debug.d_IsErrorPart'45'String_18)
                        (coe ("Bug in ctxBindingClause" :: Data.Text.Text)) in
              coe
                (case coe v3 of
                   (:) v5 v6
                     -> coe
                          MAlonzo.Code.Class.Monad.Core.d_return_20
                          MAlonzo.Code.Meta.Init.d_iMonad'45'TC_4 () erased v5 v1
                   _ -> coe v4 v1)))
