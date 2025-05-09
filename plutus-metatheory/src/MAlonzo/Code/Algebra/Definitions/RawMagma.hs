{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Algebra.Definitions.RawMagma where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles.Raw qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Definitions.RawMagma._∣ˡ_
d__'8739''737'__26 a0 a1 a2 a3 a4 = ()
data T__'8739''737'__26 = C__'44'__40 AgdaAny AgdaAny
-- Algebra.Definitions.RawMagma._∣ˡ_.quotient
d_quotient_36 :: T__'8739''737'__26 -> AgdaAny
d_quotient_36 v0
  = case coe v0 of
      C__'44'__40 v1 v2 -> coe v1
      _                 -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Definitions.RawMagma._∣ˡ_.equality
d_equality_38 :: T__'8739''737'__26 -> AgdaAny
d_equality_38 v0
  = case coe v0 of
      C__'44'__40 v1 v2 -> coe v2
      _                 -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Definitions.RawMagma._∤ˡ_
d__'8740''737'__42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  AgdaAny -> AgdaAny -> ()
d__'8740''737'__42 = erased
-- Algebra.Definitions.RawMagma._∣ʳ_
d__'8739''691'__52 a0 a1 a2 a3 a4 = ()
data T__'8739''691'__52 = C__'44'__66 AgdaAny AgdaAny
-- Algebra.Definitions.RawMagma._∣ʳ_.quotient
d_quotient_62 :: T__'8739''691'__52 -> AgdaAny
d_quotient_62 v0
  = case coe v0 of
      C__'44'__66 v1 v2 -> coe v1
      _                 -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Definitions.RawMagma._∣ʳ_.equality
d_equality_64 :: T__'8739''691'__52 -> AgdaAny
d_equality_64 v0
  = case coe v0 of
      C__'44'__66 v1 v2 -> coe v2
      _                 -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Definitions.RawMagma._∤ʳ_
d__'8740''691'__68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  AgdaAny -> AgdaAny -> ()
d__'8740''691'__68 = erased
-- Algebra.Definitions.RawMagma._∣_
d__'8739'__74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  AgdaAny -> AgdaAny -> ()
d__'8739'__74 = erased
-- Algebra.Definitions.RawMagma._∤_
d__'8740'__76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  AgdaAny -> AgdaAny -> ()
d__'8740'__76 = erased
-- Algebra.Definitions.RawMagma._∣∣_
d__'8739''8739'__82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  AgdaAny -> AgdaAny -> ()
d__'8739''8739'__82 = erased
-- Algebra.Definitions.RawMagma._∤∤_
d__'8740''8740'__88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36 ->
  AgdaAny -> AgdaAny -> ()
d__'8740''8740'__88 = erased
