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

module MAlonzo.Code.Agda.Builtin.Char where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Char
import qualified Data.Text

-- Agda.Builtin.Char.Char
type T_Char_6 = Char
d_Char_6
  = error
      "MAlonzo Runtime Error: postulate evaluated: Agda.Builtin.Char.Char"
-- Agda.Builtin.Char.primIsLower
d_primIsLower_8 = Data.Char.isLower
-- Agda.Builtin.Char.primIsDigit
d_primIsDigit_10 = Data.Char.isDigit
-- Agda.Builtin.Char.primIsAlpha
d_primIsAlpha_12 = Data.Char.isAlpha
-- Agda.Builtin.Char.primIsSpace
d_primIsSpace_14 = Data.Char.isSpace
-- Agda.Builtin.Char.primIsAscii
d_primIsAscii_16 = Data.Char.isAscii
-- Agda.Builtin.Char.primIsLatin1
d_primIsLatin1_18 = Data.Char.isLatin1
-- Agda.Builtin.Char.primIsPrint
d_primIsPrint_20 = Data.Char.isPrint
-- Agda.Builtin.Char.primIsHexDigit
d_primIsHexDigit_22 = Data.Char.isHexDigit
-- Agda.Builtin.Char.primToUpper
d_primToUpper_24 = Data.Char.toUpper
-- Agda.Builtin.Char.primToLower
d_primToLower_26 = Data.Char.toLower
-- Agda.Builtin.Char.primCharToNat
d_primCharToNat_28 = (fromIntegral . fromEnum :: Char -> Integer)
-- Agda.Builtin.Char.primNatToChar
d_primNatToChar_30 = MAlonzo.RTE.natToChar
-- Agda.Builtin.Char.primCharEquality
d_primCharEquality_32
  = (\ x y -> ((==) :: Char -> Char -> Bool) ( x) ( y))
