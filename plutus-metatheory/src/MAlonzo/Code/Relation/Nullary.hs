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

module MAlonzo.Code.Relation.Nullary where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Nullary.Irrelevant
d_Irrelevant_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_Irrelevant_8 = erased
-- Relation.Nullary.WeaklyDecidable
d_WeaklyDecidable_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_WeaklyDecidable_16 = erased
