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

module MAlonzo.Code.Data.Bool.ListAction where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base

-- Data.Bool.ListAction.and
d_and_10 :: [Bool] -> Bool
d_and_10
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe MAlonzo.Code.Data.Bool.Base.d__'8743'__24)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
-- Data.Bool.ListAction.or
d_or_12 :: [Bool] -> Bool
d_or_12
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216
      (coe MAlonzo.Code.Data.Bool.Base.d__'8744'__30)
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
-- Data.Bool.ListAction.any
d_any_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Bool) -> [AgdaAny] -> Bool
d_any_14 ~v0 ~v1 v2 v3 = du_any_14 v2 v3
du_any_14 :: (AgdaAny -> Bool) -> [AgdaAny] -> Bool
du_any_14 v0 v1
  = coe
      d_or_12
      (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v0) (coe v1))
-- Data.Bool.ListAction.all
d_all_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> Bool) -> [AgdaAny] -> Bool
d_all_18 ~v0 ~v1 v2 v3 = du_all_18 v2 v3
du_all_18 :: (AgdaAny -> Bool) -> [AgdaAny] -> Bool
du_all_18 v0 v1
  = coe
      d_and_10
      (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v0) (coe v1))
