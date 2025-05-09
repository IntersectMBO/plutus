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

module MAlonzo.Code.Text.Printf.Generic where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Char qualified
import MAlonzo.Code.Agda.Builtin.List qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Builtin.String qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.List.Base qualified
import MAlonzo.Code.Data.Product.Nary.NonDependent qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Function.Nary.NonDependent.Base qualified
import MAlonzo.Code.Text.Format.Generic qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Text.Printf.Generic.PrintfSpec
d_PrintfSpec_18 a0 a1 a2 = ()
data T_PrintfSpec_18
  = C_PrintfSpec'46'constructor_113 (AgdaAny -> AgdaAny -> AgdaAny)
                                    (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny)
-- Text.Printf.Generic._.ArgType
d_ArgType_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  () -> AgdaAny -> ()
d_ArgType_30 = erased
-- Text.Printf.Generic.PrintfSpec._.ArgChunk
d_ArgChunk_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  () -> T_PrintfSpec_18 -> ()
d_ArgChunk_42 = erased
-- Text.Printf.Generic.PrintfSpec._.ArgType
d_ArgType_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  () -> T_PrintfSpec_18 -> AgdaAny -> ()
d_ArgType_44 = erased
-- Text.Printf.Generic.PrintfSpec._.lexArg
d_lexArg_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  () ->
  T_PrintfSpec_18 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe AgdaAny
d_lexArg_46 ~v0 v1 ~v2 ~v3 = du_lexArg_46 v1
du_lexArg_46 ::
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe AgdaAny
du_lexArg_46 v0
  = coe MAlonzo.Code.Text.Format.Generic.d_lexArg_18 (coe v0)
-- Text.Printf.Generic.PrintfSpec.renderArg
d_renderArg_50 :: T_PrintfSpec_18 -> AgdaAny -> AgdaAny -> AgdaAny
d_renderArg_50 v0
  = case coe v0 of
      C_PrintfSpec'46'constructor_113 v1 v2 -> coe v1
      _                                     -> MAlonzo.RTE.mazUnreachableError
-- Text.Printf.Generic.PrintfSpec.renderStr
d_renderStr_52 ::
  T_PrintfSpec_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_renderStr_52 v0
  = case coe v0 of
      C_PrintfSpec'46'constructor_113 v1 v2 -> coe v2
      _                                     -> MAlonzo.RTE.mazUnreachableError
-- Text.Printf.Generic.Type._.Format
d_Format_64 ::
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 -> ()
d_Format_64 = erased
-- Text.Printf.Generic.Type._.Error
d_Error_66 a0 = ()
-- Text.Printf.Generic.Type.Error
d_Error_96 a0 a1 a2 = ()
data T_Error_96 = C_Error'46'constructor_421
-- Text.Printf.Generic.Type.Size
d_Size_100 ::
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Integer
d_Size_100 ~v0 v1 = du_Size_100 v1
du_Size_100 :: MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Integer
du_Size_100 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe (0 :: Integer)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe MAlonzo.Code.Text.Format.Generic.du_size_68 v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Text.Printf.Generic.Type.Printf
d_Printf_108 ::
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> () -> ()
d_Printf_108 = erased
-- Text.Printf.Generic.Type.map
d_map_118 ::
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map_118 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 = du_map_118 v5 v6 v7
du_map_118 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map_118 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
        -> coe
             MAlonzo.Code.Function.Nary.NonDependent.Base.du_map'8345'_140
             (coe
                MAlonzo.Code.Data.List.Base.du_foldr_216 (coe addInt)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Data.List.Base.du_map_22
                   (coe
                      (\ v4 ->
                         let v5 = 1 :: Integer in
                         coe
                           (case coe v4 of
                              MAlonzo.Code.Text.Format.Generic.C_Raw_64 v6 -> coe (0 :: Integer)
                              _                                            -> coe v5)))
                   (coe v3)))
             (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Text.Printf.Generic.Render._.ArgChunk
d_ArgChunk_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  T_PrintfSpec_18 -> ()
d_ArgChunk_142 = erased
-- Text.Printf.Generic.Render._.ArgType
d_ArgType_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  T_PrintfSpec_18 -> AgdaAny -> ()
d_ArgType_144 = erased
-- Text.Printf.Generic.Render._.lexArg
d_lexArg_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  T_PrintfSpec_18 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe AgdaAny
d_lexArg_146 ~v0 ~v1 v2 ~v3 = du_lexArg_146 v2
du_lexArg_146 ::
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe AgdaAny
du_lexArg_146 v0
  = coe MAlonzo.Code.Text.Format.Generic.d_lexArg_18 (coe v0)
-- Text.Printf.Generic.Render._.renderArg
d_renderArg_148 :: T_PrintfSpec_18 -> AgdaAny -> AgdaAny -> AgdaAny
d_renderArg_148 v0 = coe d_renderArg_50 (coe v0)
-- Text.Printf.Generic.Render._.renderStr
d_renderStr_150 ::
  T_PrintfSpec_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_renderStr_150 v0 = coe d_renderStr_52 (coe v0)
-- Text.Printf.Generic.Render._.Error
d_Error_154 a0 a1 a2 a3 a4 a5 = ()
-- Text.Printf.Generic.Render._.Printf
d_Printf_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  T_PrintfSpec_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> () -> ()
d_Printf_156 = erased
-- Text.Printf.Generic.Render._.map
d_map_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  T_PrintfSpec_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map_158 ~v0 ~v1 ~v2 ~v3 = du_map_158
du_map_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map_158 v0 v1 v2 v3 v4 v5 v6 = coe du_map_118 v4 v5 v6
-- Text.Printf.Generic.Render._.lexer
d_lexer_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  T_PrintfSpec_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_lexer_178 ~v0 ~v1 v2 ~v3 = du_lexer_178 v2
du_lexer_178 ::
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_lexer_178 v0
  = coe MAlonzo.Code.Text.Format.Generic.d_lexer_88 (coe v0)
-- Text.Printf.Generic.Render._.⟦_⟧
d_'10214'_'10215'_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  T_PrintfSpec_18 ->
  [MAlonzo.Code.Text.Format.Generic.T_Chunk_60] -> AgdaAny
d_'10214'_'10215'_182 ~v0 ~v1 ~v2 ~v3 = du_'10214'_'10215'_182
du_'10214'_'10215'_182 ::
  [MAlonzo.Code.Text.Format.Generic.T_Chunk_60] -> AgdaAny
du_'10214'_'10215'_182
  = coe MAlonzo.Code.Text.Format.Generic.du_'10214'_'10215'_74
-- Text.Printf.Generic.Render.assemble
d_assemble_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  T_PrintfSpec_18 ->
  [MAlonzo.Code.Text.Format.Generic.T_Chunk_60] ->
  AgdaAny -> [AgdaAny]
d_assemble_198 ~v0 ~v1 ~v2 v3 v4 v5 = du_assemble_198 v3 v4 v5
du_assemble_198 ::
  T_PrintfSpec_18 ->
  [MAlonzo.Code.Text.Format.Generic.T_Chunk_60] ->
  AgdaAny -> [AgdaAny]
du_assemble_198 v0 v1 v2
  = case coe v1 of
      [] -> coe v1
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Text.Format.Generic.C_Arg_62 v5
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe d_renderArg_50 v0 v5 v6)
                           (coe du_assemble_198 (coe v0) (coe v4) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Text.Format.Generic.C_Raw_64 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe d_renderStr_52 v0 v5)
                    (coe du_assemble_198 (coe v0) (coe v4) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Text.Printf.Generic.Render.printf′
d_printf'8242'_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  T_PrintfSpec_18 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_printf'8242'_218 ~v0 ~v1 ~v2 v3 v4 = du_printf'8242'_218 v3 v4
du_printf'8242'_218 ::
  T_PrintfSpec_18 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_printf'8242'_218 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> erased
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> coe
             MAlonzo.Code.Data.Product.Nary.NonDependent.du_curry'8868''8345'_170
             (coe
                MAlonzo.Code.Data.List.Base.du_foldr_216 (coe addInt)
                (coe (0 :: Integer))
                (coe
                   MAlonzo.Code.Data.List.Base.du_map_22
                   (coe
                      (\ v3 ->
                         let v4 = 1 :: Integer in
                         coe
                           (case coe v3 of
                              MAlonzo.Code.Text.Format.Generic.C_Raw_64 v5 -> coe (0 :: Integer)
                              _                                            -> coe v4)))
                   (coe v2)))
             (coe du_assemble_198 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Text.Printf.Generic.Render.printf
d_printf_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  T_PrintfSpec_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
d_printf_226 ~v0 ~v1 v2 v3 v4 = du_printf_226 v2 v3 v4
du_printf_226 ::
  MAlonzo.Code.Text.Format.Generic.T_FormatSpec_6 ->
  T_PrintfSpec_18 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny
du_printf_226 v0 v1 v2
  = coe
      du_printf'8242'_218 (coe v1)
      (coe MAlonzo.Code.Text.Format.Generic.d_lexer_88 (coe v0) (coe v2))
