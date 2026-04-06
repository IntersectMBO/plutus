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

module MAlonzo.Code.Text.Printf where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Text.Format
import qualified MAlonzo.Code.Text.Format.Generic
import qualified MAlonzo.Code.Text.Printf.Generic

-- Text.Printf.printfSpec
d_printfSpec_4 :: MAlonzo.Code.Text.Printf.Generic.T_PrintfSpec_18
d_printfSpec_4
  = coe
      MAlonzo.Code.Text.Printf.Generic.C_constructor_54
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
d_Printf_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> () -> ()
d_Printf_12 = erased
-- Text.Printf.Printf.map
d_map_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map_14 v0 v1 v2 v3 v4 v5 v6
  = coe MAlonzo.Code.Text.Printf.Generic.du_map_122 v4 v5 v6
-- Text.Printf._.assemble
d_assemble_20 ::
  [MAlonzo.Code.Text.Format.Generic.T_Chunk_62] ->
  AgdaAny -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_assemble_20
  = coe
      MAlonzo.Code.Text.Printf.Generic.du_assemble_204
      (coe d_printfSpec_4)
-- Text.Printf._.printf
d_printf_22 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_printf_22
  = coe
      MAlonzo.Code.Text.Printf.Generic.du_printf_232
      (coe MAlonzo.Code.Text.Format.d_formatSpec_22) (coe d_printfSpec_4)
-- Text.Printf.printf
d_printf_26 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_printf_26 v0
  = coe
      MAlonzo.Code.Text.Printf.Generic.du_map_122
      (coe
         MAlonzo.Code.Text.Format.Generic.d_lexer_90
         (coe MAlonzo.Code.Text.Format.d_formatSpec_22) (coe v0))
      (coe MAlonzo.Code.Data.String.Base.d_concat_28)
      (coe
         MAlonzo.Code.Text.Printf.Generic.du_printf_232
         (coe MAlonzo.Code.Text.Format.d_formatSpec_22) (coe d_printfSpec_4)
         (coe v0))
