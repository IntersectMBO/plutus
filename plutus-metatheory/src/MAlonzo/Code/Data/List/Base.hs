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

module MAlonzo.Code.Data.List.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.These.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.List.Base.map
d_map_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
d_map_22 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_map_22 v4 v5
du_map_22 :: (AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
du_map_22 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0 v2)
             (coe du_map_22 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base._++_
d__'43''43'__32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d__'43''43'__32 ~v0 ~v1 v2 v3 = du__'43''43'__32 v2 v3
du__'43''43'__32 :: [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du__'43''43'__32 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe du__'43''43'__32 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.intersperse
d_intersperse_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> [AgdaAny] -> [AgdaAny]
d_intersperse_42 ~v0 ~v1 v2 v3 = du_intersperse_42 v2 v3
du_intersperse_42 :: AgdaAny -> [AgdaAny] -> [AgdaAny]
du_intersperse_42 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                        (coe du_intersperse_42 (coe v0) (coe v3))) in
           coe
             (case coe v3 of
                [] -> coe v1
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.intercalate
d_intercalate_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [[AgdaAny]] -> [AgdaAny]
d_intercalate_56 ~v0 ~v1 v2 v3 = du_intercalate_56 v2 v3
du_intercalate_56 :: [AgdaAny] -> [[AgdaAny]] -> [AgdaAny]
du_intercalate_56 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> let v4
                 = coe
                     du__'43''43'__32 (coe v2)
                     (coe
                        du__'43''43'__32 (coe v0)
                        (coe du_intercalate_56 (coe v0) (coe v3))) in
           coe
             (case coe v3 of
                [] -> coe v2
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.cartesianProductWith
d_cartesianProductWith_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d_cartesianProductWith_70 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_cartesianProductWith_70 v6 v7 v8
du_cartesianProductWith_70 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du_cartesianProductWith_70 v0 v1 v2
  = case coe v1 of
      [] -> coe v1
      (:) v3 v4
        -> coe
             du__'43''43'__32 (coe du_map_22 (coe v0 v3) (coe v2))
             (coe du_cartesianProductWith_70 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.cartesianProduct
d_cartesianProduct_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] -> [AgdaAny] -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_cartesianProduct_82 ~v0 ~v1 ~v2 ~v3 = du_cartesianProduct_82
du_cartesianProduct_82 ::
  [AgdaAny] -> [AgdaAny] -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_cartesianProduct_82
  = coe
      du_cartesianProductWith_70
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32)
-- Data.List.Base.alignWith
d_alignWith_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d_alignWith_84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_alignWith_84 v6 v7 v8
du_alignWith_84 ::
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du_alignWith_84 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             du_map_22
             (coe
                MAlonzo.Code.Function.Base.du__'8728''8242'__216 (coe v0)
                (coe MAlonzo.Code.Data.These.Base.C_that_50))
             (coe v2)
      (:) v3 v4
        -> case coe v2 of
             []
               -> coe
                    du_map_22
                    (coe
                       MAlonzo.Code.Function.Base.du__'8728''8242'__216 (coe v0)
                       (coe MAlonzo.Code.Data.These.Base.C_this_48))
                    (coe v1)
             (:) v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       v0 (coe MAlonzo.Code.Data.These.Base.C_these_52 (coe v3) (coe v5)))
                    (coe du_alignWith_84 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.zipWith
d_zipWith_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d_zipWith_104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_zipWith_104 v6 v7 v8
du_zipWith_104 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du_zipWith_104 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v1 of
         (:) v4 v5
           -> case coe v2 of
                (:) v6 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0 v4 v6)
                       (coe du_zipWith_104 (coe v0) (coe v5) (coe v7))
                _ -> coe v3
         _ -> coe v3)
-- Data.List.Base.unalignWith
d_unalignWith_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.These.Base.T_These_38) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unalignWith_118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_unalignWith_118 v6 v7
du_unalignWith_118 ::
  (AgdaAny -> MAlonzo.Code.Data.These.Base.T_These_38) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unalignWith_118 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v1)
      (:) v2 v3
        -> let v4 = coe v0 v2 in
           coe
             (case coe v4 of
                MAlonzo.Code.Data.These.Base.C_this_48 v5
                  -> coe
                       MAlonzo.Code.Data.Product.Base.du_map'8321'_138
                       (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5))
                       (coe du_unalignWith_118 (coe v0) (coe v3))
                MAlonzo.Code.Data.These.Base.C_that_50 v5
                  -> coe
                       MAlonzo.Code.Data.Product.Base.du_map'8322'_150
                       (\ v6 -> coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5))
                       (coe du_unalignWith_118 (coe v0) (coe v3))
                MAlonzo.Code.Data.These.Base.C_these_52 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Product.Base.du_map_128
                       (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5))
                       (coe
                          (\ v7 ->
                             coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)))
                       (coe du_unalignWith_118 (coe v0) (coe v3))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.unzipWith
d_unzipWith_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzipWith_166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_unzipWith_166 v6 v7
du_unzipWith_166 ::
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzipWith_166 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v1)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Product.Base.du_zip_198
             (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22)
             (coe (\ v4 v5 -> coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22))
             (coe v0 v2) (coe du_unzipWith_166 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.partitionSumsWith
d_partitionSumsWith_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_partitionSumsWith_176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_partitionSumsWith_176 v6
du_partitionSumsWith_176 ::
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_partitionSumsWith_176 v0
  = coe
      du_unalignWith_118
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8242'__216
         (coe MAlonzo.Code.Data.These.Base.du_fromSum_54) (coe v0))
-- Data.List.Base.align
d_align_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] -> [AgdaAny] -> [MAlonzo.Code.Data.These.Base.T_These_38]
d_align_180 ~v0 ~v1 ~v2 ~v3 = du_align_180
du_align_180 ::
  [AgdaAny] -> [AgdaAny] -> [MAlonzo.Code.Data.These.Base.T_These_38]
du_align_180 = coe du_alignWith_84 (coe (\ v0 -> v0))
-- Data.List.Base.zip
d_zip_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] -> [AgdaAny] -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_zip_182 ~v0 ~v1 ~v2 ~v3 = du_zip_182
du_zip_182 ::
  [AgdaAny] -> [AgdaAny] -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_zip_182
  = coe
      du_zipWith_104 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32)
-- Data.List.Base.unalign
d_unalign_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Data.These.Base.T_These_38] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unalign_184 ~v0 ~v1 ~v2 ~v3 = du_unalign_184
du_unalign_184 ::
  [MAlonzo.Code.Data.These.Base.T_These_38] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unalign_184 = coe du_unalignWith_118 (coe (\ v0 -> v0))
-- Data.List.Base.unzip
d_unzip_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzip_186 ~v0 ~v1 ~v2 ~v3 = du_unzip_186
du_unzip_186 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzip_186 = coe du_unzipWith_166 (coe (\ v0 -> v0))
-- Data.List.Base.partitionSums
d_partitionSums_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_partitionSums_188 ~v0 ~v1 ~v2 ~v3 = du_partitionSums_188
du_partitionSums_188 ::
  [MAlonzo.Code.Data.Sum.Base.T__'8846'__30] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_partitionSums_188
  = coe du_partitionSumsWith_176 (coe (\ v0 -> v0))
-- Data.List.Base.merge
d_merge_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d_merge_192 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_merge_192 v4 v5 v6
du_merge_192 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du_merge_192 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v2 of
             [] -> coe v1
             (:) v5 v6
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe v0 v3 v5))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                       (coe du_merge_192 (coe v0) (coe v4) (coe v2)))
                    (coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                       (coe du_merge_192 (coe v0) (coe v1) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.foldr
d_foldr_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_foldr_216 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_foldr_216 v4 v5 v6
du_foldr_216 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
du_foldr_216 v0 v1 v2
  = case coe v2 of
      [] -> coe v1
      (:) v3 v4
        -> coe v0 v3 (coe du_foldr_216 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.foldl
d_foldl_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
d_foldl_230 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_foldl_230 v4 v5 v6
du_foldl_230 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> [AgdaAny] -> AgdaAny
du_foldl_230 v0 v1 v2
  = case coe v2 of
      [] -> coe v1
      (:) v3 v4 -> coe du_foldl_230 (coe v0) (coe v0 v1 v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.concat
d_concat_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [[AgdaAny]] -> [AgdaAny]
d_concat_244 ~v0 ~v1 = du_concat_244
du_concat_244 :: [[AgdaAny]] -> [AgdaAny]
du_concat_244
  = coe
      du_foldr_216 (coe du__'43''43'__32)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Data.List.Base.concatMap
d_concatMap_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
d_concatMap_246 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_concatMap_246 v4 v5
du_concatMap_246 ::
  (AgdaAny -> [AgdaAny]) -> [AgdaAny] -> [AgdaAny]
du_concatMap_246 v0 v1
  = coe du_concat_244 (coe du_map_22 (coe v0) (coe v1))
-- Data.List.Base.ap
d_ap_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny -> AgdaAny] -> [AgdaAny] -> [AgdaAny]
d_ap_250 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_ap_250 v4 v5
du_ap_250 :: [AgdaAny -> AgdaAny] -> [AgdaAny] -> [AgdaAny]
du_ap_250 v0 v1
  = coe
      du_concatMap_246 (coe (\ v2 -> coe du_map_22 (coe v2) (coe v1)))
      (coe v0)
-- Data.List.Base.catMaybes
d_catMaybes_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [Maybe AgdaAny] -> [AgdaAny]
d_catMaybes_256 ~v0 ~v1 = du_catMaybes_256
du_catMaybes_256 :: [Maybe AgdaAny] -> [AgdaAny]
du_catMaybes_256
  = coe
      du_foldr_216
      (coe
         MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_44
         (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22) (\ v0 -> v0))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Data.List.Base.mapMaybe
d_mapMaybe_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Maybe AgdaAny) -> [AgdaAny] -> [AgdaAny]
d_mapMaybe_258 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_mapMaybe_258 v4 v5
du_mapMaybe_258 ::
  (AgdaAny -> Maybe AgdaAny) -> [AgdaAny] -> [AgdaAny]
du_mapMaybe_258 v0 v1
  = coe du_catMaybes_256 (coe du_map_22 (coe v0) (coe v1))
-- Data.List.Base.null
d_null_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> [AgdaAny] -> Bool
d_null_262 ~v0 ~v1 v2 = du_null_262 v2
du_null_262 :: [AgdaAny] -> Bool
du_null_262 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      (:) v1 v2 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.length
d_length_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Integer
d_length_268 ~v0 ~v1 = du_length_268
du_length_268 :: [AgdaAny] -> Integer
du_length_268
  = coe
      du_foldr_216
      (let v0 = \ v0 -> addInt (coe (1 :: Integer)) (coe v0) in
       coe (coe (\ v1 -> v0)))
      (coe (0 :: Integer))
-- Data.List.Base.[_]
d_'91'_'93'_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> [AgdaAny]
d_'91'_'93'_270 ~v0 ~v1 v2 = du_'91'_'93'_270 v2
du_'91'_'93'_270 :: AgdaAny -> [AgdaAny]
du_'91'_'93'_270 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Data.List.Base.fromMaybe
d_fromMaybe_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Maybe AgdaAny -> [AgdaAny]
d_fromMaybe_274 ~v0 ~v1 v2 = du_fromMaybe_274 v2
du_fromMaybe_274 :: Maybe AgdaAny -> [AgdaAny]
du_fromMaybe_274 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_'91'_'93'_270 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.replicate
d_replicate_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> AgdaAny -> [AgdaAny]
d_replicate_278 ~v0 ~v1 v2 v3 = du_replicate_278 v2 v3
du_replicate_278 :: Integer -> AgdaAny -> [AgdaAny]
du_replicate_278 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                (coe du_replicate_278 (coe v2) (coe v1)))
-- Data.List.Base.iterate
d_iterate_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> Integer -> [AgdaAny]
d_iterate_286 ~v0 ~v1 v2 v3 v4 = du_iterate_286 v2 v3 v4
du_iterate_286 ::
  (AgdaAny -> AgdaAny) -> AgdaAny -> Integer -> [AgdaAny]
du_iterate_286 v0 v1 v2
  = case coe v2 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                (coe du_iterate_286 (coe v0) (coe v0 v1) (coe v3)))
-- Data.List.Base.inits
d_inits_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [[AgdaAny]]
d_inits_298 ~v0 ~v1 v2 = du_inits_298 v2
du_inits_298 :: [AgdaAny] -> [[AgdaAny]]
du_inits_298 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe du_tail_304 (coe v0))
-- Data.List.Base.Inits.tail
d_tail_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [[AgdaAny]]
d_tail_304 ~v0 ~v1 v2 = du_tail_304 v2
du_tail_304 :: [AgdaAny] -> [[AgdaAny]]
du_tail_304 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe du_'91'_'93'_270 (coe v1))
             (coe
                du_map_22
                (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1))
                (coe du_tail_304 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.tails
d_tails_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [[AgdaAny]]
d_tails_314 ~v0 ~v1 v2 = du_tails_314 v2
du_tails_314 :: [AgdaAny] -> [[AgdaAny]]
du_tails_314 v0
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
      (coe du_tail_320 (coe v0))
-- Data.List.Base.Tails.tail
d_tail_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [[AgdaAny]]
d_tail_320 ~v0 ~v1 v2 = du_tail_320 v2
du_tail_320 :: [AgdaAny] -> [[AgdaAny]]
du_tail_320 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe du_tail_320 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.insertAt
d_insertAt_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> [AgdaAny]
d_insertAt_328 ~v0 ~v1 v2 v3 v4 = du_insertAt_328 v2 v3 v4
du_insertAt_328 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> [AgdaAny]
du_insertAt_328 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v0)
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
        -> case coe v0 of
             (:) v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                    (coe du_insertAt_328 (coe v6) (coe v4) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.updateAt
d_updateAt_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) -> [AgdaAny]
d_updateAt_344 ~v0 ~v1 v2 v3 v4 = du_updateAt_344 v2 v3 v4
du_updateAt_344 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) -> [AgdaAny]
du_updateAt_344 v0 v1 v2
  = case coe v0 of
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2 v3) (coe v4)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                    (coe du_updateAt_344 (coe v4) (coe v6) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.applyUpTo
d_applyUpTo_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (Integer -> AgdaAny) -> Integer -> [AgdaAny]
d_applyUpTo_360 ~v0 ~v1 v2 v3 = du_applyUpTo_360 v2 v3
du_applyUpTo_360 :: (Integer -> AgdaAny) -> Integer -> [AgdaAny]
du_applyUpTo_360 v0 v1
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe v0 (0 :: Integer))
                (coe
                   du_applyUpTo_360
                   (coe (\ v3 -> coe v0 (addInt (coe (1 :: Integer)) (coe v3))))
                   (coe v2)))
-- Data.List.Base.applyDownFrom
d_applyDownFrom_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (Integer -> AgdaAny) -> Integer -> [AgdaAny]
d_applyDownFrom_368 ~v0 ~v1 v2 v3 = du_applyDownFrom_368 v2 v3
du_applyDownFrom_368 ::
  (Integer -> AgdaAny) -> Integer -> [AgdaAny]
du_applyDownFrom_368 v0 v1
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0 v2)
                (coe du_applyDownFrom_368 (coe v0) (coe v2)))
-- Data.List.Base.tabulate
d_tabulate_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> [AgdaAny]
d_tabulate_380 ~v0 ~v1 v2 v3 = du_tabulate_380 v2 v3
du_tabulate_380 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> [AgdaAny]
du_tabulate_380 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                (coe
                   du_tabulate_380 (coe v2)
                   (coe
                      (\ v3 -> coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v3)))))
-- Data.List.Base.lookup
d_lookup_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_lookup_390 ~v0 ~v1 v2 v3 = du_lookup_390 v2 v3
du_lookup_390 ::
  [AgdaAny] -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_lookup_390 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v2
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
               -> coe du_lookup_390 (coe v3) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.upTo
d_upTo_402 :: Integer -> [Integer]
d_upTo_402 = coe du_applyUpTo_360 (coe (\ v0 -> v0))
-- Data.List.Base.downFrom
d_downFrom_404 :: Integer -> [Integer]
d_downFrom_404 = coe du_applyDownFrom_368 (coe (\ v0 -> v0))
-- Data.List.Base.allFin
d_allFin_408 :: Integer -> [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_allFin_408 v0 = coe du_tabulate_380 (coe v0) (coe (\ v1 -> v1))
-- Data.List.Base.unfold
d_unfold_420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Integer -> ()) ->
  (Integer ->
   AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> AgdaAny -> [AgdaAny]
d_unfold_420 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_unfold_420 v4 v5 v6
du_unfold_420 ::
  (Integer ->
   AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer -> AgdaAny -> [AgdaAny]
du_unfold_420 v0 v1 v2
  = case coe v1 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_44
                (\ v4 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4))
                     (coe
                        du_unfold_420 (coe v0) (coe v3)
                        (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v0 v3 v2))
-- Data.List.Base.reverseAcc
d_reverseAcc_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d_reverseAcc_442 ~v0 ~v1 = du_reverseAcc_442
du_reverseAcc_442 :: [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du_reverseAcc_442
  = coe
      du_foldl_230
      (coe
         (\ v0 v1 ->
            coe
              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v0)))
-- Data.List.Base.reverse
d_reverse_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny]
d_reverse_444 ~v0 ~v1 = du_reverse_444
du_reverse_444 :: [AgdaAny] -> [AgdaAny]
du_reverse_444
  = coe
      du_reverseAcc_442
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Data.List.Base._ʳ++_
d__'691''43''43'__446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d__'691''43''43'__446 ~v0 ~v1 v2 v3 = du__'691''43''43'__446 v2 v3
du__'691''43''43'__446 :: [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du__'691''43''43'__446 v0 v1 = coe du_reverseAcc_442 v1 v0
-- Data.List.Base._∷ʳ_
d__'8759''691'__448 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> AgdaAny -> [AgdaAny]
d__'8759''691'__448 ~v0 ~v1 v2 v3 = du__'8759''691'__448 v2 v3
du__'8759''691'__448 :: [AgdaAny] -> AgdaAny -> [AgdaAny]
du__'8759''691'__448 v0 v1
  = coe du__'43''43'__32 (coe v0) (coe du_'91'_'93'_270 (coe v1))
-- Data.List.Base.InitLast
d_InitLast_458 a0 a1 a2 = ()
data T_InitLast_458
  = C_'91''93'_462 | C__'8759''691''8242'__468 [AgdaAny] AgdaAny
-- Data.List.Base.initLast
d_initLast_472 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> T_InitLast_458
d_initLast_472 ~v0 ~v1 v2 = du_initLast_472 v2
du_initLast_472 :: [AgdaAny] -> T_InitLast_458
du_initLast_472 v0
  = case coe v0 of
      [] -> coe C_'91''93'_462
      (:) v1 v2
        -> let v3 = coe du_initLast_472 (coe v2) in
           coe
             (case coe v3 of
                C_'91''93'_462
                  -> coe
                       C__'8759''691''8242'__468
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1)
                C__'8759''691''8242'__468 v4 v5
                  -> coe
                       C__'8759''691''8242'__468
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v4))
                       (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.unsnoc
d_unsnoc_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unsnoc_494 ~v0 ~v1 v2 = du_unsnoc_494 v2
du_unsnoc_494 ::
  [AgdaAny] -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unsnoc_494 v0
  = let v1 = coe du_initLast_472 (coe v0) in
    coe
      (case coe v1 of
         C_'91''93'_462 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         C__'8759''691''8242'__468 v2 v3
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.List.Base.uncons
d_uncons_510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_uncons_510 ~v0 ~v1 v2 = du_uncons_510 v2
du_uncons_510 ::
  [AgdaAny] -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_uncons_510 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.head
d_head_516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Maybe AgdaAny
d_head_516 ~v0 ~v1 v2 = du_head_516 v2
du_head_516 :: [AgdaAny] -> Maybe AgdaAny
du_head_516 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.tail
d_tail_520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Maybe [AgdaAny]
d_tail_520 ~v0 ~v1 v2 = du_tail_520 v2
du_tail_520 :: [AgdaAny] -> Maybe [AgdaAny]
du_tail_520 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.last
d_last_524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Maybe AgdaAny
d_last_524 ~v0 ~v1 v2 = du_last_524 v2
du_last_524 :: [AgdaAny] -> Maybe AgdaAny
du_last_524 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> let v3 = coe du_last_524 (coe v2) in
           coe
             (case coe v2 of
                [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.take
d_take_530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> [AgdaAny] -> [AgdaAny]
d_take_530 ~v0 ~v1 v2 v3 = du_take_530 v2 v3
du_take_530 :: Integer -> [AgdaAny] -> [AgdaAny]
du_take_530 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                [] -> coe v1
                (:) v3 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                       (coe du_take_530 (coe v2) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.List.Base.drop
d_drop_542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> [AgdaAny] -> [AgdaAny]
d_drop_542 ~v0 ~v1 v2 v3 = du_drop_542 v2 v3
du_drop_542 :: Integer -> [AgdaAny] -> [AgdaAny]
du_drop_542 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                [] -> coe v1
                (:) v3 v4 -> coe du_drop_542 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.List.Base.splitAt
d_splitAt_554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_splitAt_554 ~v0 ~v1 v2 v3 = du_splitAt_554 v2 v3
du_splitAt_554 ::
  Integer -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_splitAt_554 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                []
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v1)
                (:) v3 v4
                  -> coe
                       MAlonzo.Code.Data.Product.Base.du_map'8321'_138
                       (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3))
                       (coe du_splitAt_554 (coe v2) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.List.Base.removeAt
d_removeAt_570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> [AgdaAny]
d_removeAt_570 ~v0 ~v1 v2 v3 = du_removeAt_570 v2 v3
du_removeAt_570 ::
  [AgdaAny] -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> [AgdaAny]
du_removeAt_570 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v3
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                    (coe du_removeAt_570 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.takeWhile
d_takeWhile_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
d_takeWhile_584 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_takeWhile_584 v4 v5
du_takeWhile_584 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
du_takeWhile_584 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> let v4
                 = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                     (coe v0 v2) in
           coe
             (if coe v4
                then coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                       (coe du_takeWhile_584 (coe v0) (coe v3))
                else coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.takeWhileᵇ
d_takeWhile'7495'_610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
d_takeWhile'7495'_610 ~v0 ~v1 v2 = du_takeWhile'7495'_610 v2
du_takeWhile'7495'_610 ::
  (AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
du_takeWhile'7495'_610 v0
  = coe
      du_takeWhile_584
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
              (coe v0 v1)))
-- Data.List.Base.dropWhile
d_dropWhile_616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
d_dropWhile_616 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_dropWhile_616 v4 v5
du_dropWhile_616 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
du_dropWhile_616 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> let v4
                 = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                     (coe v0 v2) in
           coe
             (if coe v4 then coe du_dropWhile_616 (coe v0) (coe v3) else coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.dropWhileᵇ
d_dropWhile'7495'_642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
d_dropWhile'7495'_642 ~v0 ~v1 v2 = du_dropWhile'7495'_642 v2
du_dropWhile'7495'_642 ::
  (AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
du_dropWhile'7495'_642 v0
  = coe
      du_dropWhile_616
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
              (coe v0 v1)))
-- Data.List.Base.filter
d_filter_648 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
d_filter_648 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_filter_648 v4 v5
du_filter_648 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
du_filter_648 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> let v4
                 = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                     (coe v0 v2) in
           coe
             (if coe v4
                then coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                       (coe du_filter_648 (coe v0) (coe v3))
                else coe du_filter_648 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.filterᵇ
d_filter'7495'_674 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
d_filter'7495'_674 ~v0 ~v1 v2 = du_filter'7495'_674 v2
du_filter'7495'_674 :: (AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
du_filter'7495'_674 v0
  = coe
      du_filter_648
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
              (coe v0 v1)))
-- Data.List.Base.partition
d_partition_680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_partition_680 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_partition_680 v4 v5
du_partition_680 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_partition_680 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v1)
      (:) v2 v3
        -> let v4
                 = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                     (coe v0 v2) in
           coe
             (let v5 = coe du_partition_680 (coe v0) (coe v3) in
              coe
                (if coe v4
                   then case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v6))
                                 (coe v7)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   else (case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                             -> coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v7))
                           _ -> MAlonzo.RTE.mazUnreachableError)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.partitionᵇ
d_partition'7495'_714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Bool) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_partition'7495'_714 ~v0 ~v1 v2 = du_partition'7495'_714 v2
du_partition'7495'_714 ::
  (AgdaAny -> Bool) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_partition'7495'_714 v0
  = coe
      du_partition_680
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
              (coe v0 v1)))
-- Data.List.Base.span
d_span_720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_span_720 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_span_720 v4 v5
du_span_720 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_span_720 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v1)
      (:) v2 v3
        -> let v4
                 = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                     (coe v0 v2) in
           coe
             (if coe v4
                then coe
                       MAlonzo.Code.Data.Product.Base.du_map_128
                       (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2))
                       (coe (\ v5 v6 -> v6)) (coe du_span_720 (coe v0) (coe v3))
                else coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.spanᵇ
d_span'7495'_754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Bool) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_span'7495'_754 ~v0 ~v1 v2 = du_span'7495'_754 v2
du_span'7495'_754 ::
  (AgdaAny -> Bool) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_span'7495'_754 v0
  = coe
      du_span_720
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
              (coe v0 v1)))
-- Data.List.Base.break
d_break_760 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_break_760 ~v0 ~v1 ~v2 ~v3 v4 = du_break_760 v4
du_break_760 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_break_760 v0
  = coe
      du_span_720
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_76
              (coe v0 v1)))
-- Data.List.Base.breakᵇ
d_break'7495'_764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Bool) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_break'7495'_764 ~v0 ~v1 v2 = du_break'7495'_764 v2
du_break'7495'_764 ::
  (AgdaAny -> Bool) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_break'7495'_764 v0
  = coe
      du_break_760
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
              (coe v0 v1)))
-- Data.List.Base.linesBy
d_linesBy_770 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [[AgdaAny]]
d_linesBy_770 ~v0 ~v1 ~v2 ~v3 v4 = du_linesBy_770 v4
du_linesBy_770 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [[AgdaAny]]
du_linesBy_770 v0
  = coe
      du_go_780 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Data.List.Base._.go
d_go_780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe [AgdaAny] -> [AgdaAny] -> [[AgdaAny]]
d_go_780 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_go_780 v4 v5 v6
du_go_780 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe [AgdaAny] -> [AgdaAny] -> [[AgdaAny]]
du_go_780 v0 v1 v2
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_44
             (coe
                MAlonzo.Code.Function.Base.du__'8728''8242'__216
                (coe du_'91'_'93'_270) (coe du_reverse_444))
             v2 v1
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28 (coe v0 v3))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe du_reverse_444 (coe du_acc'8242'_794 (coe v1)))
                (coe
                   du_go_780 (coe v0)
                   (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) (coe v4)))
             (coe
                du_go_780 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                      (coe du_acc'8242'_794 (coe v1))))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base._._.acc′
d_acc'8242'_794 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe [AgdaAny] -> AgdaAny -> [AgdaAny] -> [AgdaAny]
d_acc'8242'_794 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7
  = du_acc'8242'_794 v5
du_acc'8242'_794 :: Maybe [AgdaAny] -> [AgdaAny]
du_acc'8242'_794 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_fromMaybe_46
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) v0
-- Data.List.Base.linesByᵇ
d_linesBy'7495'_796 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Bool) -> [AgdaAny] -> [[AgdaAny]]
d_linesBy'7495'_796 ~v0 ~v1 v2 = du_linesBy'7495'_796 v2
du_linesBy'7495'_796 ::
  (AgdaAny -> Bool) -> [AgdaAny] -> [[AgdaAny]]
du_linesBy'7495'_796 v0
  = coe
      du_linesBy_770
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
              (coe v0 v1)))
-- Data.List.Base.wordsBy
d_wordsBy_802 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [[AgdaAny]]
d_wordsBy_802 ~v0 ~v1 ~v2 ~v3 v4 = du_wordsBy_802 v4
du_wordsBy_802 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [[AgdaAny]]
du_wordsBy_802 v0
  = coe
      du_go_820 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Data.List.Base._.cons
d_cons_812 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [[AgdaAny]] -> [[AgdaAny]]
d_cons_812 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_cons_812 v5 v6
du_cons_812 :: [AgdaAny] -> [[AgdaAny]] -> [[AgdaAny]]
du_cons_812 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
              (coe du_reverse_444 v0) (coe v1) in
    coe
      (case coe v0 of
         [] -> coe v1
         _ -> coe v2)
-- Data.List.Base._.go
d_go_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny] -> [[AgdaAny]]
d_go_820 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_go_820 v4 v5 v6
du_go_820 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny] -> [[AgdaAny]]
du_go_820 v0 v1 v2
  = case coe v2 of
      [] -> coe du_cons_812 (coe v1) (coe v2)
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28 (coe v0 v3))
             (coe
                du_cons_812 (coe v1)
                (coe
                   du_go_820 (coe v0)
                   (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v4)))
             (coe
                du_go_820 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v1))
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.wordsByᵇ
d_wordsBy'7495'_830 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Bool) -> [AgdaAny] -> [[AgdaAny]]
d_wordsBy'7495'_830 ~v0 ~v1 v2 = du_wordsBy'7495'_830 v2
du_wordsBy'7495'_830 ::
  (AgdaAny -> Bool) -> [AgdaAny] -> [[AgdaAny]]
du_wordsBy'7495'_830 v0
  = coe
      du_wordsBy_802
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
              (coe v0 v1)))
-- Data.List.Base.derun
d_derun_836 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
d_derun_836 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_derun_836 v4 v5
du_derun_836 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
du_derun_836 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v3 of
             [] -> coe v1
             (:) v4 v5
               -> let v6
                        = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                            (coe v0 v2 v4) in
                  coe
                    (let v7 = coe du_derun_836 (coe v0) (coe v3) in
                     coe
                       (if coe v6
                          then coe v7
                          else coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.derunᵇ
d_derun'7495'_876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
d_derun'7495'_876 ~v0 ~v1 v2 = du_derun'7495'_876 v2
du_derun'7495'_876 ::
  (AgdaAny -> AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
du_derun'7495'_876 v0
  = coe
      du_derun_836
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8322'__92
         (coe
            (\ v1 v2 ->
               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72))
         (coe v0))
-- Data.List.Base.deduplicate
d_deduplicate_882 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
d_deduplicate_882 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_deduplicate_882 v4 v5
du_deduplicate_882 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [AgdaAny]
du_deduplicate_882 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe
                du_filter_648
                (coe
                   (\ v4 ->
                      coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_76
                        (coe v0 v2 v4)))
                (coe du_deduplicate_882 (coe v0) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.deduplicateᵇ
d_deduplicate'7495'_892 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
d_deduplicate'7495'_892 ~v0 ~v1 v2 = du_deduplicate'7495'_892 v2
du_deduplicate'7495'_892 ::
  (AgdaAny -> AgdaAny -> Bool) -> [AgdaAny] -> [AgdaAny]
du_deduplicate'7495'_892 v0
  = coe
      du_deduplicate_882
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8322'__92
         (coe
            (\ v1 v2 ->
               MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72))
         (coe v0))
-- Data.List.Base.find
d_find_898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> Maybe AgdaAny
d_find_898 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_find_898 v4 v5
du_find_898 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> Maybe AgdaAny
du_find_898 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28 (coe v0 v2))
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2))
             (coe du_find_898 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.findᵇ
d_find'7495'_908 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Bool) -> [AgdaAny] -> Maybe AgdaAny
d_find'7495'_908 ~v0 ~v1 v2 = du_find'7495'_908 v2
du_find'7495'_908 ::
  (AgdaAny -> Bool) -> [AgdaAny] -> Maybe AgdaAny
du_find'7495'_908 v0
  = coe
      du_find_898
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
              (coe v0 v1)))
-- Data.List.Base.findIndex
d_findIndex_916 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_findIndex_916 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_findIndex_916 v4 v5
du_findIndex_916 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_findIndex_916 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28 (coe v0 v2))
             (coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
             (coe
                MAlonzo.Code.Data.Maybe.Base.du_map_64
                (coe MAlonzo.Code.Data.Fin.Base.C_suc_16)
                (coe du_findIndex_916 (coe v0) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.findIndexᵇ
d_findIndex'7495'_928 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Bool) ->
  [AgdaAny] -> Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_findIndex'7495'_928 ~v0 ~v1 v2 = du_findIndex'7495'_928 v2
du_findIndex'7495'_928 ::
  (AgdaAny -> Bool) ->
  [AgdaAny] -> Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_findIndex'7495'_928 v0
  = coe
      du_findIndex_916
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
              (coe v0 v1)))
-- Data.List.Base.findIndices
d_findIndices_936 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_findIndices_936 v0 ~v1 v2 ~v3 v4 v5
  = du_findIndices_936 v0 v2 v4 v5
du_findIndices_936 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_findIndices_936 v0 v1 v2 v3
  = case coe v3 of
      [] -> coe v3
      (:) v4 v5
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28 (coe v2 v4))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                (coe du_indices_950 (coe v0) (coe v1) (coe v2) (coe v5)))
             (coe du_indices_950 (coe v0) (coe v1) (coe v2) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base._.indices
d_indices_950 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> [AgdaAny] -> [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_indices_950 v0 ~v1 v2 ~v3 v4 ~v5 v6 = du_indices_950 v0 v2 v4 v6
du_indices_950 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_indices_950 v0 v1 v2 v3
  = coe
      du_map_22 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16)
      (coe du_findIndices_936 (coe v0) (coe v1) (coe v2) (coe v3))
-- Data.List.Base.findIndicesᵇ
d_findIndices'7495'_954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> Bool) ->
  [AgdaAny] -> [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
d_findIndices'7495'_954 v0 ~v1 v2 = du_findIndices'7495'_954 v0 v2
du_findIndices'7495'_954 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> Bool) ->
  [AgdaAny] -> [MAlonzo.Code.Data.Fin.Base.T_Fin_10]
du_findIndices'7495'_954 v0 v1
  = coe
      du_findIndices_936 (coe v0) (coe ())
      (coe
         (\ v2 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
              (coe v1 v2)))
-- Data.List.Base._[_]%=_
d__'91'_'93''37''61'__960 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) -> [AgdaAny]
d__'91'_'93''37''61'__960 ~v0 ~v1 v2 v3 v4
  = du__'91'_'93''37''61'__960 v2 v3 v4
du__'91'_'93''37''61'__960 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) -> [AgdaAny]
du__'91'_'93''37''61'__960 v0 v1 v2
  = coe du_updateAt_344 (coe v0) (coe v1) (coe v2)
-- Data.List.Base._[_]∷=_
d__'91'_'93''8759''61'__970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> [AgdaAny]
d__'91'_'93''8759''61'__970 ~v0 ~v1 v2 v3 v4
  = du__'91'_'93''8759''61'__970 v2 v3 v4
du__'91'_'93''8759''61'__970 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> [AgdaAny]
du__'91'_'93''8759''61'__970 v0 v1 v2
  = coe
      du__'91'_'93''37''61'__960 (coe v0) (coe v1) (coe (\ v3 -> v2))
-- Data.List.Base._?∷_
d__'63''8759'__978 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Maybe AgdaAny -> [AgdaAny] -> [AgdaAny]
d__'63''8759'__978 ~v0 ~v1 = du__'63''8759'__978
du__'63''8759'__978 :: Maybe AgdaAny -> [AgdaAny] -> [AgdaAny]
du__'63''8759'__978
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_44
      (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22) (\ v0 -> v0)
-- Data.List.Base._∷ʳ?_
d__'8759''691''63'__980 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Maybe AgdaAny -> [AgdaAny]
d__'8759''691''63'__980 ~v0 ~v1 v2 v3
  = du__'8759''691''63'__980 v2 v3
du__'8759''691''63'__980 :: [AgdaAny] -> Maybe AgdaAny -> [AgdaAny]
du__'8759''691''63'__980 v0 v1
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe'8242'_44
      (coe du__'8759''691'__448 (coe v0)) v0 v1
-- Data.List.Base._.++-rawMagma
d_'43''43''45'rawMagma_996 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'43''43''45'rawMagma_996 ~v0 ~v1 = du_'43''43''45'rawMagma_996
du_'43''43''45'rawMagma_996 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
du_'43''43''45'rawMagma_996
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_68
      (coe du__'43''43'__32)
-- Data.List.Base._.++-[]-rawMonoid
d_'43''43''45''91''93''45'rawMonoid_998 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74
d_'43''43''45''91''93''45'rawMonoid_998 ~v0 ~v1
  = du_'43''43''45''91''93''45'rawMonoid_998
du_'43''43''45''91''93''45'rawMonoid_998 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74
du_'43''43''45''91''93''45'rawMonoid_998
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_102
      (coe du__'43''43'__32)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Data.List.Base._∷ʳ'_
d__'8759''691'''__1004 :: [AgdaAny] -> AgdaAny -> T_InitLast_458
d__'8759''691'''__1004 = coe C__'8759''691''8242'__468
-- Data.List.Base._─_
d__'9472'__1006 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> [AgdaAny]
d__'9472'__1006 v0 v1 v2 v3 = coe du_removeAt_570 v2 v3
-- Data.List.Base.scanr
d_scanr_1008 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> [AgdaAny]
d_scanr_1008 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_scanr_1008 v4 v5 v6
du_scanr_1008 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> [AgdaAny]
du_scanr_1008 v0 v1 v2
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v2)
      (:) v3 v4
        -> let v5 = coe du_scanr_1008 (coe v0) (coe v1) (coe v4) in
           coe
             (case coe v5 of
                [] -> coe v5
                (:) v6 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0 v3 v6)
                       (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.scanl
d_scanl_1046 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> [AgdaAny]
d_scanl_1046 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_scanl_1046 v4 v5 v6
du_scanl_1046 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> [AgdaAny]
du_scanl_1046 v0 v1 v2
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v2)
      (:) v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe du_scanl_1046 (coe v0) (coe v0 v1 v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Base.and
d_and_1060 :: [Bool] -> Bool
d_and_1060
  = coe
      du_foldr_216 (coe MAlonzo.Code.Data.Bool.Base.d__'8743'__24)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
-- Data.List.Base.all
d_all_1062 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Bool) -> [AgdaAny] -> Bool
d_all_1062 ~v0 ~v1 v2 v3 = du_all_1062 v2 v3
du_all_1062 :: (AgdaAny -> Bool) -> [AgdaAny] -> Bool
du_all_1062 v0 v1
  = coe d_and_1060 (coe du_map_22 (coe v0) (coe v1))
-- Data.List.Base.or
d_or_1066 :: [Bool] -> Bool
d_or_1066
  = coe
      du_foldr_216 (coe MAlonzo.Code.Data.Bool.Base.d__'8744'__30)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Data.List.Base.any
d_any_1068 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Bool) -> [AgdaAny] -> Bool
d_any_1068 ~v0 ~v1 v2 v3 = du_any_1068 v2 v3
du_any_1068 :: (AgdaAny -> Bool) -> [AgdaAny] -> Bool
du_any_1068 v0 v1 = coe d_or_1066 (coe du_map_22 (coe v0) (coe v1))
-- Data.List.Base.sum
d_sum_1072 :: [Integer] -> Integer
d_sum_1072 = coe du_foldr_216 (coe addInt) (coe (0 :: Integer))
-- Data.List.Base.product
d_product_1074 :: [Integer] -> Integer
d_product_1074 = coe du_foldr_216 (coe mulInt) (coe (1 :: Integer))
