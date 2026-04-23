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

module MAlonzo.Code.Untyped.Relation.Binary.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Untyped

-- Untyped.Relation.Binary.Core.Relation
d_Relation_8 :: ()
d_Relation_8 = erased
-- Untyped.Relation.Binary.Core.Relation*
d_Relation'42'_12 :: ()
d_Relation'42'_12 = erased
-- Untyped.Relation.Binary.Core.Pointwise
d_Pointwise_20 a0 a1 a2 a3 = ()
data T_Pointwise_20
  = C_'91''93'_26 | C__'8759'__36 AgdaAny T_Pointwise_20
-- Untyped.Relation.Binary.Core.DecidableRel
d_DecidableRel_38 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_DecidableRel_38 = erased
