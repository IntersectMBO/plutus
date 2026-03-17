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

module MAlonzo.Code.Meta.Prelude where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.List.Base

-- Meta.Prelude.lookupᵇ
d_lookup'7495'_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> Maybe AgdaAny
d_lookup'7495'_18 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_lookup'7495'_18 v4 v5 v6
du_lookup'7495'_18 ::
  (AgdaAny -> AgdaAny -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  AgdaAny -> Maybe AgdaAny
du_lookup'7495'_18 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v0 v5 v2)
                    (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v6))
                    (coe du_lookup'7495'_18 (coe v0) (coe v4) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Meta.Prelude.zipWithIndex
d_zipWithIndex_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (Integer -> AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
d_zipWithIndex_34 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_zipWithIndex_34 v4 v5
du_zipWithIndex_34 ::
  (Integer -> AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
du_zipWithIndex_34 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_zipWith_104 (coe v0)
      (coe
         MAlonzo.Code.Data.List.Base.d_upTo_402
         (coe MAlonzo.Code.Data.List.Base.du_length_268 v1))
      (coe v1)
-- Meta.Prelude.enumerate
d_enumerate_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_enumerate_44 ~v0 ~v1 = du_enumerate_44
du_enumerate_44 ::
  [AgdaAny] -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_enumerate_44
  = coe
      du_zipWithIndex_34
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32)
-- Meta.Prelude._⁉_
d__'8265'__46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Integer -> Maybe AgdaAny
d__'8265'__46 v0 ~v1 = du__'8265'__46 v0
du__'8265'__46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [AgdaAny] -> Integer -> Maybe AgdaAny
du__'8265'__46 v0 = coe du_'46'extendedlambda0_48 (coe v0)
-- Meta.Prelude..extendedlambda0
d_'46'extendedlambda0_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> Integer -> Maybe AgdaAny
d_'46'extendedlambda0_48 v0 ~v1 v2 v3
  = du_'46'extendedlambda0_48 v0 v2 v3
du_'46'extendedlambda0_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [AgdaAny] -> Integer -> Maybe AgdaAny
du_'46'extendedlambda0_48 v0 v1 v2
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v3 v4
        -> case coe v2 of
             0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
             _ -> let v5 = subInt (coe v2) (coe (1 :: Integer)) in
                  coe (coe du__'8265'__46 v0 v4 v5)
      _ -> MAlonzo.RTE.mazUnreachableError
