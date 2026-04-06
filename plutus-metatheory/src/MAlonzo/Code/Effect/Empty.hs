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

module MAlonzo.Code.Effect.Empty where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Effect.Empty.RawEmpty
d_RawEmpty_16 a0 a1 a2 = ()
newtype T_RawEmpty_16 = C_constructor_26 (() -> AgdaAny)
-- Effect.Empty.RawEmpty.empty
d_empty_22 :: T_RawEmpty_16 -> () -> AgdaAny
d_empty_22 v0
  = case coe v0 of
      C_constructor_26 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Empty.RawEmpty.∅
d_'8709'_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawEmpty_16 -> () -> AgdaAny
d_'8709'_24 ~v0 ~v1 ~v2 v3 ~v4 = du_'8709'_24 v3
du_'8709'_24 :: T_RawEmpty_16 -> AgdaAny
du_'8709'_24 v0 = coe d_empty_22 v0 erased
