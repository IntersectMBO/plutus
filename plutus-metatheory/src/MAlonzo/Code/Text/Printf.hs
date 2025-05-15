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

module MAlonzo.Code.Text.Printf where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Float qualified
import MAlonzo.Code.Agda.Builtin.String qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Integer.Show qualified
import MAlonzo.Code.Data.Nat.Show qualified
import MAlonzo.Code.Data.String.Base qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Text.Format qualified
import MAlonzo.Code.Text.Format.Generic qualified
import MAlonzo.Code.Text.Printf.Generic qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Text.Printf.printfSpec
d_printfSpec_4 :: MAlonzo.Code.Text.Printf.Generic.T_PrintfSpec_18
d_printfSpec_4
  = coe
      MAlonzo.Code.Text.Printf.Generic.C_PrintfSpec'46'constructor_113
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Text.Format.C_ℕArg_6
                -> coe MAlonzo.Code.Data.Nat.Show.d_show_56
              MAlonzo.Code.Text.Format.C_ℤArg_8
                -> coe MAlonzo.Code.Data.Integer.Show.d_show_6
              MAlonzo.Code.Text.Format.C_FloatArg_10
                -> coe MAlonzo.Code.Agda.Builtin.Float.d_primShowFloat_46
              MAlonzo.Code.Text.Format.C_CharArg_12
                -> coe MAlonzo.Code.Data.String.Base.d_fromChar_16
              MAlonzo.Code.Text.Format.C_StringArg_14 -> coe (\ v1 -> v1)
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe (\ v0 -> v0))
-- Text.Printf.Printf.Error
d_Error_8 a0 a1 = ()
-- Text.Printf.Printf.Printf
d_Printf_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> () -> ()
d_Printf_10 = erased
-- Text.Printf.Printf.map
d_map_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map_12 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Text.Printf.Generic.du_map_118 v4 v5 v6
-- Text.Printf._.assemble
d_assemble_18 ::
  [MAlonzo.Code.Text.Format.Generic.T_Chunk_60] ->
  AgdaAny -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_assemble_18
  = coe
      MAlonzo.Code.Text.Printf.Generic.du_assemble_198
      (coe d_printfSpec_4)
-- Text.Printf._.printf
d_printf_20 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_printf_20
  = coe
      MAlonzo.Code.Text.Printf.Generic.du_printf_226
      (coe MAlonzo.Code.Text.Format.d_formatSpec_22) (coe d_printfSpec_4)
-- Text.Printf.printf
d_printf_24 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_printf_24 v0
  = coe
      MAlonzo.Code.Text.Printf.Generic.du_map_118
      (coe
         MAlonzo.Code.Text.Format.Generic.d_lexer_88
         (coe MAlonzo.Code.Text.Format.d_formatSpec_22) (coe v0))
      (coe MAlonzo.Code.Data.String.Base.d_concat_28)
      (coe
         MAlonzo.Code.Text.Printf.Generic.du_printf_226
         (coe MAlonzo.Code.Text.Format.d_formatSpec_22) (coe d_printfSpec_4)
         (coe v0))
