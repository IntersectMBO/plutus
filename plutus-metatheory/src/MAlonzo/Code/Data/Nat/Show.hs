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

module MAlonzo.Code.Data.Nat.Show where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Digit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Effectful
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Maybe.Effectful
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Function.Base

-- Data.Nat.Show.readMaybe
d_readMaybe_10 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe Integer
d_readMaybe_10 v0 ~v1 v2 = du_readMaybe_10 v0 v2
du_readMaybe_10 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Maybe Integer
du_readMaybe_10 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Function.Base.du__'8728''8242'__216
              (coe
                 MAlonzo.Code.Data.Maybe.Base.du_map_64
                 (coe du_convert_18 (coe v0)))
              (coe
                 MAlonzo.Code.Function.Base.du__'8728''8242'__216
                 (coe
                    MAlonzo.Code.Data.List.Effectful.du_mapA_94
                    (coe MAlonzo.Code.Data.Maybe.Effectful.du_applicative_24)
                    (coe du_readDigit_32 (coe v0)))
                 (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12))
              (coe v1) in
    coe
      (case coe v1 of
         l | (==) l ("" :: Data.Text.Text) ->
             coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
         _ -> coe v2)
-- Data.Nat.Show._.convert
d_convert_18 :: Integer -> AgdaAny -> [Integer] -> Integer
d_convert_18 v0 ~v1 = du_convert_18 v0
du_convert_18 :: Integer -> [Integer] -> Integer
du_convert_18 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_foldl_230
      (coe (\ v1 -> addInt (coe mulInt (coe v0) (coe v1))))
      (coe (0 :: Integer))
-- Data.Nat.Show._.char0
d_char0_24 :: Integer -> AgdaAny -> Integer
d_char0_24 ~v0 ~v1 = du_char0_24
du_char0_24 :: Integer
du_char0_24
  = coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 '0'
-- Data.Nat.Show._.char9
d_char9_26 :: Integer -> AgdaAny -> Integer
d_char9_26 ~v0 ~v1 = du_char9_26
du_char9_26 :: Integer
du_char9_26
  = coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 '9'
-- Data.Nat.Show._.chara
d_chara_28 :: Integer -> AgdaAny -> Integer
d_chara_28 ~v0 ~v1 = du_chara_28
du_chara_28 :: Integer
du_chara_28
  = coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 'a'
-- Data.Nat.Show._.charf
d_charf_30 :: Integer -> AgdaAny -> Integer
d_charf_30 ~v0 ~v1 = du_charf_30
du_charf_30 :: Integer
du_charf_30
  = coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 'f'
-- Data.Nat.Show._.readDigit
d_readDigit_32 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe Integer
d_readDigit_32 v0 ~v1 v2 = du_readDigit_32 v0 v2
du_readDigit_32 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe Integer
du_readDigit_32 v0 v1
  = coe
      MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72
      (coe du_digit_46 (coe v1))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Data.Maybe.Base.du_when_88
              (coe ltInt (coe v2) (coe v0)) (coe v2)))
-- Data.Nat.Show._._.charc
d_charc_40 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Integer
d_charc_40 ~v0 ~v1 v2 = du_charc_40 v2
du_charc_40 :: MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Integer
du_charc_40 v0
  = coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0
-- Data.Nat.Show._._.dec
d_dec_42 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe Integer
d_dec_42 ~v0 ~v1 v2 = du_dec_42 v2
du_dec_42 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe Integer
du_dec_42 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_when_88
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe du_char0_24)
            (coe du_charc_40 (coe v0)))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
            (coe du_charc_40 (coe v0)) (coe du_char9_26)))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (coe du_charc_40 (coe v0)) (coe du_char0_24))
-- Data.Nat.Show._._.hex
d_hex_44 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe Integer
d_hex_44 ~v0 ~v1 v2 = du_hex_44 v2
du_hex_44 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe Integer
du_hex_44 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_when_88
      (coe
         MAlonzo.Code.Data.Bool.Base.d__'8743'__24
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14 (coe du_chara_28)
            (coe du_charc_40 (coe v0)))
         (coe
            MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
            (coe du_charc_40 (coe v0)) (coe du_charf_30)))
      (coe
         MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
         (addInt (coe (10 :: Integer)) (coe du_charc_40 (coe v0)))
         (coe du_chara_28))
-- Data.Nat.Show._._.digit
d_digit_46 ::
  Integer ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe Integer
d_digit_46 ~v0 ~v1 v2 = du_digit_46 v2
du_digit_46 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe Integer
du_digit_46 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du__'60''8739''62'__80
      (coe du_dec_42 (coe v0)) (coe du_hex_44 (coe v0))
-- Data.Nat.Show.toDigitChar
d_toDigitChar_50 ::
  Integer -> MAlonzo.Code.Agda.Builtin.Char.T_Char_6
d_toDigitChar_50 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Char.d_primNatToChar_30
      (addInt
         (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 '0')
         (coe v0))
-- Data.Nat.Show.toDecimalChars
d_toDecimalChars_54 ::
  Integer -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_toDecimalChars_54
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe d_toDigitChar_50))
      (coe
         MAlonzo.Code.Data.Digit.du_toNatDigits_20 (coe (10 :: Integer)))
-- Data.Nat.Show.show
d_show_56 :: Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_show_56
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14)
      (coe d_toDecimalChars_54)
-- Data.Nat.Show.charsInBase
d_charsInBase_64 ::
  Integer ->
  AgdaAny ->
  AgdaAny -> Integer -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
d_charsInBase_64 v0 ~v1 ~v2 v3 = du_charsInBase_64 v0 v3
du_charsInBase_64 ::
  Integer -> Integer -> [MAlonzo.Code.Agda.Builtin.Char.T_Char_6]
du_charsInBase_64 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe MAlonzo.Code.Data.Digit.du_showDigit_198)
      (coe
         MAlonzo.Code.Data.List.Base.du_reverse_444
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe MAlonzo.Code.Data.Digit.du_toDigits_84 (coe v0) (coe v1))))
-- Data.Nat.Show.showInBase
d_showInBase_78 ::
  Integer ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showInBase_78 v0 ~v1 ~v2 v3 = du_showInBase_78 v0 v3
du_showInBase_78 ::
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_showInBase_78 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
      (coe du_charsInBase_64 (coe v0) (coe v1))
