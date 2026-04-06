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

module MAlonzo.Code.Data.These.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Sum.Base

-- Data.These.Base.These
d_These_38 a0 a1 a2 a3 = ()
data T_These_38
  = C_this_48 AgdaAny | C_that_50 AgdaAny |
    C_these_52 AgdaAny AgdaAny
-- Data.These.Base.fromSum
d_fromSum_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_These_38
d_fromSum_54 ~v0 ~v1 ~v2 ~v3 = du_fromSum_54
du_fromSum_54 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_These_38
du_fromSum_54
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
      (coe C_this_48) (coe C_that_50)
-- Data.These.Base.map
d_map_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_These_38 -> T_These_38
d_map_60 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_map_60 v8 v9 v10
du_map_60 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T_These_38 -> T_These_38
du_map_60 v0 v1 v2
  = case coe v2 of
      C_this_48 v3 -> coe C_this_48 (coe v0 v3)
      C_that_50 v3 -> coe C_that_50 (coe v1 v3)
      C_these_52 v3 v4 -> coe C_these_52 (coe v0 v3) (coe v1 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.These.Base.map₁
d_map'8321'_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> T_These_38 -> T_These_38
d_map'8321'_84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_map'8321'_84 v6
du_map'8321'_84 :: (AgdaAny -> AgdaAny) -> T_These_38 -> T_These_38
du_map'8321'_84 v0 = coe du_map_60 (coe v0) (coe (\ v1 -> v1))
-- Data.These.Base.map₂
d_map'8322'_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> T_These_38 -> T_These_38
d_map'8322'_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_map'8322'_90
du_map'8322'_90 :: (AgdaAny -> AgdaAny) -> T_These_38 -> T_These_38
du_map'8322'_90 = coe du_map_60 (coe (\ v0 -> v0))
-- Data.These.Base.fold
d_fold_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_These_38 -> AgdaAny
d_fold_92 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_fold_92 v6 v7 v8 v9
du_fold_92 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_These_38 -> AgdaAny
du_fold_92 v0 v1 v2 v3
  = case coe v3 of
      C_this_48 v4 -> coe v0 v4
      C_that_50 v4 -> coe v1 v4
      C_these_52 v4 v5 -> coe v2 v4 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.These.Base.foldWithDefaults
d_foldWithDefaults_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_These_38 -> AgdaAny
d_foldWithDefaults_120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_foldWithDefaults_120 v6 v7 v8
du_foldWithDefaults_120 ::
  AgdaAny ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_These_38 -> AgdaAny
du_foldWithDefaults_120 v0 v1 v2
  = coe du_fold_92 (coe (\ v3 -> coe v2 v3 v1)) (coe v2 v0) (coe v2)
-- Data.These.Base.swap
d_swap_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_These_38 -> T_These_38
d_swap_128 ~v0 ~v1 ~v2 ~v3 = du_swap_128
du_swap_128 :: T_These_38 -> T_These_38
du_swap_128
  = coe
      du_fold_92 (coe C_that_50) (coe C_this_48)
      (coe (\ v0 v1 -> coe C_these_52 (coe v1) (coe v0)))
-- Data.These.Base.alignWith
d_alignWith_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (T_These_38 -> AgdaAny) ->
  (T_These_38 -> AgdaAny) -> T_These_38 -> T_These_38 -> T_These_38
d_alignWith_130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12 v13 v14 v15
  = du_alignWith_130 v12 v13 v14 v15
du_alignWith_130 ::
  (T_These_38 -> AgdaAny) ->
  (T_These_38 -> AgdaAny) -> T_These_38 -> T_These_38 -> T_These_38
du_alignWith_130 v0 v1 v2 v3
  = case coe v2 of
      C_this_48 v4
        -> case coe v3 of
             C_this_48 v5
               -> coe C_this_48 (coe v0 (coe C_these_52 (coe v4) (coe v5)))
             C_that_50 v5 -> coe C_these_52 (coe v0 v2) (coe v1 v3)
             C_these_52 v5 v6
               -> coe
                    C_these_52 (coe v0 (coe C_these_52 (coe v4) (coe v5)))
                    (coe v1 (coe C_that_50 (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_that_50 v4
        -> case coe v3 of
             C_this_48 v5
               -> coe
                    C_these_52 (coe v0 (coe C_that_50 (coe v5)))
                    (coe v1 (coe C_this_48 (coe v4)))
             C_that_50 v5
               -> coe C_that_50 (coe v1 (coe C_these_52 (coe v4) (coe v5)))
             C_these_52 v5 v6
               -> coe
                    C_these_52 (coe v0 (coe C_that_50 (coe v5)))
                    (coe v1 (coe C_these_52 (coe v4) (coe v6)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_these_52 v4 v5
        -> case coe v3 of
             C_this_48 v6
               -> coe
                    C_these_52 (coe v0 (coe C_these_52 (coe v4) (coe v6)))
                    (coe v1 (coe C_this_48 (coe v5)))
             C_that_50 v6
               -> coe
                    C_these_52 (coe v0 (coe C_this_48 (coe v4)))
                    (coe v1 (coe C_these_52 (coe v5) (coe v6)))
             C_these_52 v6 v7
               -> coe
                    C_these_52 (coe v0 (coe C_these_52 (coe v4) (coe v6)))
                    (coe v1 (coe C_these_52 (coe v5) (coe v7)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.These.Base.align
d_align_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_These_38 -> T_These_38 -> T_These_38
d_align_216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 = du_align_216
du_align_216 :: T_These_38 -> T_These_38 -> T_These_38
du_align_216
  = coe du_alignWith_130 (coe (\ v0 -> v0)) (coe (\ v0 -> v0))
