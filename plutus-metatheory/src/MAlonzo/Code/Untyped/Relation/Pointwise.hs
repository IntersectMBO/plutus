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

module MAlonzo.Code.Untyped.Relation.Pointwise where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Untyped

-- Untyped.Relation.Pointwise.Pointwise
d_Pointwise_10 a0 a1 a2 a3 = ()
data T_Pointwise_10
  = C_'91''93'_16 | C__'8759'__26 AgdaAny T_Pointwise_10
-- Untyped.Relation.Pointwise.pointwise-refl
d_pointwise'45'refl_34 ::
  Integer ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny) ->
  T_Pointwise_10
d_pointwise'45'refl_34 v0 ~v1 v2 v3
  = du_pointwise'45'refl_34 v0 v2 v3
du_pointwise'45'refl_34 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny) ->
  T_Pointwise_10
du_pointwise'45'refl_34 v0 v1 v2
  = case coe v1 of
      [] -> coe C_'91''93'_16
      (:) v3 v4
        -> coe
             C__'8759'__26 (coe v2 v0 v3)
             (coe du_pointwise'45'refl_34 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
