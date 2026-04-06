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

module MAlonzo.Code.Text.Format.Generic where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.ListAction
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.Sum.Effectful.Left
import qualified MAlonzo.Code.Effect.Applicative
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Function.Strict
import qualified MAlonzo.Code.Level

-- Text.Format.Generic.FormatSpec
d_FormatSpec_6 = ()
newtype T_FormatSpec_6
  = C_constructor_20 (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
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
      C_constructor_20 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Text.Format.Generic._.unionSpec
d_unionSpec_26 ::
  T_FormatSpec_6 -> T_FormatSpec_6 -> T_FormatSpec_6
d_unionSpec_26 v0 v1
  = coe
      C_constructor_20
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
d_ArgChunk_56 :: T_FormatSpec_6 -> ()
d_ArgChunk_56 = erased
-- Text.Format.Generic.Format._.ArgType
d_ArgType_58 :: T_FormatSpec_6 -> AgdaAny -> ()
d_ArgType_58 = erased
-- Text.Format.Generic.Format._.lexArg
d_lexArg_60 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Maybe AgdaAny
d_lexArg_60 v0 = coe d_lexArg_18 (coe v0)
-- Text.Format.Generic.Format.Chunk
d_Chunk_62 a0 = ()
data T_Chunk_62
  = C_Arg_64 AgdaAny |
    C_Raw_66 MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Text.Format.Generic.Format.Format
d_Format_68 :: T_FormatSpec_6 -> ()
d_Format_68 = erased
-- Text.Format.Generic.Format.size
d_size_70 :: T_FormatSpec_6 -> [T_Chunk_62] -> Integer
d_size_70 ~v0 = du_size_70
du_size_70 :: [T_Chunk_62] -> Integer
du_size_70
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe MAlonzo.Code.Data.Nat.ListAction.d_sum_6)
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe
            (\ v0 ->
               let v1 = 1 :: Integer in
               coe
                 (case coe v0 of
                    C_Raw_66 v2 -> coe (0 :: Integer)
                    _ -> coe v1))))
-- Text.Format.Generic.Format.⟦_⟧
d_'10214'_'10215'_76 :: T_FormatSpec_6 -> [T_Chunk_62] -> AgdaAny
d_'10214'_'10215'_76 ~v0 v1 = du_'10214'_'10215'_76 v1
du_'10214'_'10215'_76 :: [T_Chunk_62] -> AgdaAny
du_'10214'_'10215'_76 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Level.C_lift_20
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      (:) v1 v2
        -> case coe v1 of
             C_Arg_64 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe du_'10214'_'10215'_76 (coe v2))
             C_Raw_66 v3 -> coe du_'10214'_'10215'_76 (coe v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Text.Format.Generic.Format.Error
d_Error_84 a0 = ()
data T_Error_84
  = C_UnexpectedEndOfString_86 MAlonzo.Code.Agda.Builtin.String.T_String_6 |
    C_InvalidType_88 MAlonzo.Code.Agda.Builtin.String.T_String_6
                     MAlonzo.Code.Agda.Builtin.Char.T_Char_6
                     MAlonzo.Code.Agda.Builtin.String.T_String_6
-- Text.Format.Generic.Format.lexer
d_lexer_90 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_lexer_90 v0 v1
  = coe
      d_loop_146 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1)
-- Text.Format.Generic.Format._.RevWord
d_RevWord_132 ::
  T_FormatSpec_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_RevWord_132 = erased
-- Text.Format.Generic.Format._.Prefix
d_Prefix_134 ::
  T_FormatSpec_6 -> MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d_Prefix_134 = erased
-- Text.Format.Generic.Format._.toRevString
d_toRevString_136 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_toRevString_136 ~v0 ~v1 = du_toRevString_136
du_toRevString_136 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_toRevString_136
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14)
      (coe MAlonzo.Code.Data.List.Base.du_reverse_444)
-- Text.Format.Generic.Format._.push
d_push_138 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [T_Chunk_62] -> [T_Chunk_62]
d_push_138 ~v0 ~v1 v2 v3 = du_push_138 v2 v3
du_push_138 ::
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [T_Chunk_62] -> [T_Chunk_62]
du_push_138 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
              (coe C_Raw_66 (coe du_toRevString_136 v0)) (coe v1) in
    coe
      (case coe v0 of
         [] -> coe v1
         _ -> coe v2)
-- Text.Format.Generic.Format._.loop
d_loop_146 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_loop_146 v0 v1 v2 v3 v4
  = case coe v4 of
      []
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
             (coe du_push_138 (coe v2) (coe v4))
      (:) v5 v6
        -> let v7
                 = d_loop_146
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
                               (coe du_push_138 (coe v2))
                               (d_type_148
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
                                        d_loop_146 (coe v0) (coe v1)
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
d_type_148 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_type_148 v0 v1 v2 v3
  = case coe v3 of
      []
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe C_UnexpectedEndOfString_86 (coe v1))
      (:) v4 v5
        -> coe
             MAlonzo.Code.Effect.Applicative.du__'8859'__70
             (coe MAlonzo.Code.Data.Sum.Effectful.Left.du_applicative_20)
             (coe
                MAlonzo.Code.Data.Sum.Base.du_map'8322'_94
                (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22)
                (coe du_chunk_186 (coe v0) (coe v2) (coe v5) (coe v4)))
             (d_loop_146
                (coe v0) (coe v1)
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v2))
                (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Text.Format.Generic.Format._._.chunk
d_chunk_186 ::
  T_FormatSpec_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_chunk_186 v0 ~v1 v2 ~v3 v4 v5 = du_chunk_186 v0 v2 v4 v5
du_chunk_186 ::
  T_FormatSpec_6 ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  [MAlonzo.Code.Agda.Builtin.Char.T_Char_6] ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_chunk_186 v0 v1 v2 v3
  = let v4 = coe d_lexArg_18 v0 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
           -> coe
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe C_Arg_64 (coe v5))
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Function.Strict.du_force'8242'_56 ()
                MAlonzo.Code.Level.d_0ℓ_22 (coe du_toRevString_136 v1)
                (\ v5 ->
                   coe
                     MAlonzo.Code.Function.Strict.du_force'8242'_56 ()
                     MAlonzo.Code.Level.d_0ℓ_22
                     (coe MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14 v2)
                     (\ v6 ->
                        coe
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                          (coe C_InvalidType_88 (coe v5) (coe v3) (coe v6))))
         _ -> MAlonzo.RTE.mazUnreachableError)
