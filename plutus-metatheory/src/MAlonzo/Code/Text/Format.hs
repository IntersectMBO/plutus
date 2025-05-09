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

module MAlonzo.Code.Text.Format where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Char qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Agda.Builtin.String qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Text.Format.Generic qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
  = coe
      MAlonzo.Code.Text.Format.Generic.C_FormatSpec'46'constructor_27
      d_lexArg_20
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
      MAlonzo.Code.Text.Format.Generic.d_lexer_88 (coe d_formatSpec_22)
-- Text.Format._.size
d_size_42 ::
  [MAlonzo.Code.Text.Format.Generic.T_Chunk_60] -> Integer
d_size_42 = coe MAlonzo.Code.Text.Format.Generic.du_size_68
-- Text.Format._.⟦_⟧
d_'10214'_'10215'_44 ::
  [MAlonzo.Code.Text.Format.Generic.T_Chunk_60] -> AgdaAny
d_'10214'_'10215'_44
  = coe MAlonzo.Code.Text.Format.Generic.du_'10214'_'10215'_74
