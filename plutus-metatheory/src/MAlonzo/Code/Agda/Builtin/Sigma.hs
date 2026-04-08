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

module MAlonzo.Code.Agda.Builtin.Sigma where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Agda.Builtin.Sigma.Σ
d_Σ_14 a0 a1 a2 a3 = ()
data T_Σ_14 = C__'44'__32 AgdaAny AgdaAny
-- Agda.Builtin.Sigma.Σ.fst
d_fst_28 :: T_Σ_14 -> AgdaAny
d_fst_28 v0
  = case coe v0 of
      C__'44'__32 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Agda.Builtin.Sigma.Σ.snd
d_snd_30 :: T_Σ_14 -> AgdaAny
d_snd_30 v0
  = case coe v0 of
      C__'44'__32 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
