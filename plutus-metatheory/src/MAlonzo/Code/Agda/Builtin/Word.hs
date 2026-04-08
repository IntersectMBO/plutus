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

module MAlonzo.Code.Agda.Builtin.Word where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Agda.Builtin.Word.Word64
type T_Word64_6 = MAlonzo.RTE.Word64
d_Word64_6
  = error
      "MAlonzo Runtime Error: postulate evaluated: Agda.Builtin.Word.Word64"
-- Agda.Builtin.Word.primWord64ToNat
d_primWord64ToNat_8 = MAlonzo.RTE.word64ToNat
-- Agda.Builtin.Word.primWord64FromNat
d_primWord64FromNat_10 = MAlonzo.RTE.word64FromNat
