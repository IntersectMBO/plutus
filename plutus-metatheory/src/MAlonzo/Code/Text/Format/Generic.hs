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

module MAlonzo.Code.Text.Format.Generic where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Char qualified
import MAlonzo.Code.Agda.Builtin.List qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Builtin.String qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Data.List.Base qualified
import MAlonzo.Code.Data.Maybe.Base qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Data.Sum.Effectful.Left qualified
import MAlonzo.Code.Effect.Applicative qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Function.Strict qualified
import MAlonzo.Code.Level qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Text.Format.Generic.FormatSpec
d_FormatSpec_6 = ()
newtype T_FormatSpec_6
  = C_FormatSpec'46'constructor_27 (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
                                    Maybe AgdaAny)
-- Text.Format.Generic.FormatSpec.ArgChunk
d_ArgChunk_14 :: T_FormatSpec_6 -> ()
d_ArgChunk_14 = erased
-- Text.Format.Generic.FormatSpec.ArgType
d_ArgType_16 :: T_FormatSpec_6 -> AgdaAny -> ()
d_ArgType_16 = erased
-- Text.Format.Generic.FormatSpec.lexArg
d_lexArg_18 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe AgdaAny
d_lexArg_18 v0
  = case coe v0 of
      C_FormatSpec'46'constructor_27 v3 -> coe v3
      _                                 -> MAlonzo.RTE.mazUnreachableError
-- Text.Format.Generic._.unionSpec
d_unionSpec_24 ::
  T_FormatSpec_6 -> T_FormatSpec_6 -> T_FormatSpec_6
d_unionSpec_24 v0 v1
  = coe
      C_FormatSpec'46'constructor_27
      (\ v2 ->
         coe
           MAlonzo.Code.Data.Maybe.Base.du__'60''8739''62'__80
           (coe
              MAlonzo.Code.Data.Maybe.Base.du_map_64
              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38)
              (coe d_lexArg_18 v0 v2))
           (coe
              MAlonzo.Code.Data.Maybe.Base.du_map_64
              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42)
              (coe d_lexArg_18 v1 v2)))
-- Text.Format.Generic.Format._.ArgChunk
d_ArgChunk_54 :: T_FormatSpec_6 -> ()
d_ArgChunk_54 = erased
-- Text.Format.Generic.Format._.ArgType
d_ArgType_56 :: T_FormatSpec_6 -> AgdaAny -> ()
d_ArgType_56 = erased
-- Text.Format.Generic.Format._.lexArg
d_lexArg_58 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe AgdaAny
d_lexArg_58 v0 = coe d_lexArg_18 (coe v0)
-- Text.Format.Generic.Format.Chunk
d_Chunk_60 a0 = ()
data T_Chunk_60
  = C_Arg_62 AgdaAny |
    C_Raw_64 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Text.Format.Generic.Format.Format
d_Format_66 :: T_FormatSpec_6 -> ()
d_Format_66 = erased
-- Text.Format.Generic.Format.size
d_size_68 :: T_FormatSpec_6 -> [T_Chunk_60] -> Integer
d_size_68 ~v0 = du_size_68
du_size_68 :: [T_Chunk_60] -> Integer
du_size_68
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe MAlonzo.Code.Data.List.Base.d_sum_280)
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v0 ->
               let v1 = 1 :: Integer in
               coe
                 (case coe v0 of
                    C_Raw_64 v2 -> coe (0 :: Integer)
                    _           -> coe v1))))
-- Text.Format.Generic.Format.⟦_⟧
d_'10214'_'10215'_74 :: T_FormatSpec_6 -> [T_Chunk_60] -> AgdaAny
d_'10214'_'10215'_74 ~v0 v1 = du_'10214'_'10215'_74 v1
du_'10214'_'10215'_74 :: [T_Chunk_60] -> AgdaAny
du_'10214'_'10215'_74 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Level.C_lift_20
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (:) v1 v2
        -> case coe v1 of
             C_Arg_62 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe du_'10214'_'10215'_74 (coe v2))
             C_Raw_64 v3 -> coe du_'10214'_'10215'_74 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Text.Format.Generic.Format.Error
d_Error_82 a0 = ()
data T_Error_82
  = C_UnexpectedEndOfString_84 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_InvalidType_86 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     MAlonzo.Code.Agda.Builtin.Char.T_Char_6
                     MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Text.Format.Generic.Format.lexer
d_lexer_88 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_lexer_88 v0 v1
  = coe
      d_loop_144 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1)
-- Text.Format.Generic.Format._.RevWord
d_RevWord_130 ::
  T_FormatSpec_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_RevWord_130 = erased
-- Text.Format.Generic.Format._.Prefix
d_Prefix_132 ::
  T_FormatSpec_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_Prefix_132 = erased
-- Text.Format.Generic.Format._.toRevString
d_toRevString_134 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_toRevString_134 ~v0 ~v1 = du_toRevString_134
du_toRevString_134 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_toRevString_134
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14)
      (coe MAlonzo.Code.Data.List.Base.du_reverse_460)
-- Text.Format.Generic.Format._.push
d_push_136 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [T_Chunk_60] -> [T_Chunk_60]
d_push_136 ~v0 ~v1 v2 v3 = du_push_136 v2 v3
du_push_136 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [T_Chunk_60] -> [T_Chunk_60]
du_push_136 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
              (coe C_Raw_64 (coe du_toRevString_134 v0)) (coe v1) in
    coe
      (case coe v0 of
         [] -> coe v1
         _  -> coe v2)
-- Text.Format.Generic.Format._.loop
d_loop_144 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_loop_144 v0 v1 v2 v3 v4
  = case coe v4 of
      []
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe du_push_136 (coe v2) (coe v4))
      (:) v5 v6
        -> let v7
                 = d_loop_144
                     (coe v0) (coe v1)
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v2))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5) (coe v3))
                     (coe v6) in
           coe
             (case coe v5 of
                '%'
                  -> let v8
                           = coe
                               MAlonzo.Code.Data.Sum.Base.du_map'8322'_94
                               (coe du_push_136 (coe v2))
                               (d_type_146
                                  (coe v0) (coe v1)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '%')
                                     (coe v3))
                                  (coe v6)) in
                     coe
                       (case coe v6 of
                          (:) v9 v10
                            -> case coe v9 of
                                 '%'
                                   -> coe
                                        d_loop_144 (coe v0) (coe v1)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '%')
                                           (coe v2))
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '%')
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe '%')
                                              (coe v3)))
                                        (coe v10)
                                 _ -> coe v8
                          _ -> coe v8)
                _ -> coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Text.Format.Generic.Format._.type
d_type_146 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_type_146 v0 v1 v2 v3
  = case coe v3 of
      []
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe C_UnexpectedEndOfString_84 (coe v1))
      (:) v4 v5
        -> coe
             MAlonzo.Code.Effect.Applicative.du__'8859'__70
             (coe MAlonzo.Code.Data.Sum.Effectful.Left.du_applicative_20)
             (coe
                MAlonzo.Code.Data.Sum.Base.du_map'8322'_94
                (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22)
                (coe du_chunk_184 (coe v0) (coe v2) (coe v5) (coe v4)))
             (d_loop_144
                (coe v0) (coe v1)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v2))
                (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Text.Format.Generic.Format._._.chunk
d_chunk_184 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_chunk_184 v0 ~v1 v2 ~v3 v4 v5 = du_chunk_184 v0 v2 v4 v5
du_chunk_184 ::
  T_FormatSpec_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_chunk_184 v0 v1 v2 v3
  = let v4 = coe d_lexArg_18 v0 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe C_Arg_62 (coe v5))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Function.Strict.du_force'8242'_56 ()
                MAlonzo.Code.Level.d_0ℓ_22 (coe du_toRevString_134 v1)
                (\ v5 ->
                   coe
                     MAlonzo.Code.Function.Strict.du_force'8242'_56 ()
                     MAlonzo.Code.Level.d_0ℓ_22
                     (coe MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14 v2)
                     (\ v6 ->
                        coe
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                          (coe C_InvalidType_86 (coe v5) (coe v3) (coe v6))))
         _ -> MAlonzo.RTE.mazUnreachableError)
