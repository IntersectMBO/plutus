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

module MAlonzo.Code.Agda.Builtin.String where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text

-- Agda.Builtin.String.String
type T_String_6 = Data.Text.Text
d_String_6
  = error
      "MAlonzo Runtime Error: postulate evaluated: Agda.Builtin.String.String"
-- Agda.Builtin.String.primStringUncons
d_primStringUncons_10 = Data.Text.uncons
-- Agda.Builtin.String.primStringToList
d_primStringToList_12 = Data.Text.unpack
-- Agda.Builtin.String.primStringFromList
d_primStringFromList_14 = Data.Text.pack
-- Agda.Builtin.String.primStringAppend
d_primStringAppend_16
  = ((Data.Text.append) :: Data.Text.Text->Data.Text.Text->Data.Text.Text)
-- Agda.Builtin.String.primStringEquality
d_primStringEquality_18
  = (\ x y -> ((==) :: Data.Text.Text -> Data.Text.Text -> Bool) ( x) ( y))
-- Agda.Builtin.String.primShowChar
d_primShowChar_20
  = (Data.Text.pack . show :: Char -> Data.Text.Text)
-- Agda.Builtin.String.primShowString
d_primShowString_22
  = (Data.Text.pack . show :: Data.Text.Text -> Data.Text.Text)
-- Agda.Builtin.String.primShowNat
d_primShowNat_24
  = (Data.Text.pack . show :: Integer -> Data.Text.Text)
