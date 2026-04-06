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

module MAlonzo.Code.Induction where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Induction.RecStruct
d_RecStruct_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> ()
d_RecStruct_20 = erased
-- Induction.RecursorBuilder
d_RecursorBuilder_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) -> ()
d_RecursorBuilder_24 = erased
-- Induction.Recursor
d_Recursor_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) -> ()
d_Recursor_30 = erased
-- Induction.build
d_build_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_build_36 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
  = du_build_36 v5 v6 v7 v8
du_build_36 ::
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_build_36 v0 v1 v2 v3 = coe v2 v3 (coe v0 v1 v2 v3)
-- Induction.SubsetRecursorBuilder
d_SubsetRecursorBuilder_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) -> ((AgdaAny -> ()) -> AgdaAny -> ()) -> ()
d_SubsetRecursorBuilder_46 = erased
-- Induction.SubsetRecursor
d_SubsetRecursor_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) -> ((AgdaAny -> ()) -> AgdaAny -> ()) -> ()
d_SubsetRecursor_54 = erased
-- Induction.subsetBuild
d_subsetBuild_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_subsetBuild_62 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 v11
  = du_subsetBuild_62 v7 v8 v9 v10 v11
du_subsetBuild_62 ::
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_subsetBuild_62 v0 v1 v2 v3 v4 = coe v2 v3 (coe v0 v1 v2 v3 v4)
