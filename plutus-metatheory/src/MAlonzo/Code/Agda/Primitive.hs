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

module MAlonzo.Code.Agda.Primitive where

import Data.Text qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Agda.Primitive.Level
type T_Level_18 = ()
d_Level_18
  = error
      "MAlonzo Runtime Error: postulate evaluated: Agda.Primitive.Level"
-- Agda.Primitive.lzero
d_lzero_20 = ()
-- Agda.Primitive.lsuc
d_lsuc_24 = (\ _ -> ())
-- Agda.Primitive._⊔_
d__'8852'__30 = (\ _ _ -> ())
