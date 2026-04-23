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
-- Untyped.Relation.Binary.Core.Pointwise
d_Pointwise_16 a0 a1 a2 a3 = ()
data T_Pointwise_16
  = C_'91''93'_22 | C__'8759'__32 AgdaAny T_Pointwise_16
-- Untyped.Relation.Binary.Core.DecidableRel
d_DecidableRel_34 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  ()
d_DecidableRel_34 = erased
-- Untyped.Relation.Binary.Core.RelationT
d_RelationT_44 :: ()
d_RelationT_44 = erased
