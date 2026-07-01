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

module MAlonzo.Code.Text.Format where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Text.Format.Generic

-- Text.Format.ArgChunk
d_ArgChunk_4 = ()
data T_ArgChunk_4
  = C_ℕArg_6 | C_ℤArg_8 | C_FloatArg_10 | C_CharArg_12 |
    C_StringArg_14
-- Text.Format.ArgType
d_ArgType_18 :: T_ArgChunk_4 -> ()
d_ArgType_18 = erased
-- Text.Format.lexArg
d_lexArg_20 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe T_ArgChunk_4
d_lexArg_20 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         'c'
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_CharArg_12)
         'd' -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_ℤArg_8)
         'f'
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_FloatArg_10)
         'i' -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_ℤArg_8)
         's'
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_StringArg_14)
         'u' -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_ℕArg_6)
         _ -> coe v1)
-- Text.Format.formatSpec
d_formatSpec_22 :: MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6
d_formatSpec_22
  = coe MAlonzo.Code.Text.Format.Generic.C_constructor_20 d_lexArg_20
-- Text.Format._.Chunk
d_Chunk_28 = ()
-- Text.Format._.Error
d_Error_30 = ()
-- Text.Format._.Format
d_Format_32 :: ()
d_Format_32 = erased
-- Text.Format._.lexer
d_lexer_40 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_lexer_40
  = coe
      MAlonzo.Code.Text.Format.Generic.d_lexer_90 (coe d_formatSpec_22)
-- Text.Format._.size
d_size_42 ::
  [MAlonzo.Code.Text.Format.Generic.T_Chunk_62] -> Integer
d_size_42 = coe MAlonzo.Code.Text.Format.Generic.du_size_70
-- Text.Format._.⟦_⟧
d_'10214'_'10215'_44 ::
  [MAlonzo.Code.Text.Format.Generic.T_Chunk_62] -> AgdaAny
d_'10214'_'10215'_44
  = coe MAlonzo.Code.Text.Format.Generic.du_'10214'_'10215'_76
