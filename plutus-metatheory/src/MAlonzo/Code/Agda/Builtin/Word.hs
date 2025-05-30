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

module MAlonzo.Code.Agda.Builtin.Word where

import Data.Text qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Agda.Builtin.Word.Word64
type T_Word64_6 = MAlonzo.RTE.Word64
d_Word64_6
  = error
      "MAlonzo Runtime Error: postulate evaluated: Agda.Builtin.Word.Word64"
-- Agda.Builtin.Word.primWord64ToNat
d_primWord64ToNat_8 = MAlonzo.RTE.word64ToNat
-- Agda.Builtin.Word.primWord64FromNat
d_primWord64FromNat_10 = MAlonzo.RTE.word64FromNat
