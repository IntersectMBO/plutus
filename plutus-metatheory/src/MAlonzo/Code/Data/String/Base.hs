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

module MAlonzo.Code.Data.String.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.NonEmpty.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.String.Base._≈_
d__'8776'__6 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d__'8776'__6 = erased
-- Data.String.Base._<_
d__'60'__8 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d__'60'__8 = erased
-- Data.String.Base._≤_
d__'8804'__10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()
d__'8804'__10 = erased
-- Data.String.Base.head
d_head_12 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Char.T_Char_6
d_head_12
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Data.Maybe.Base.du_map_64
         (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0))))
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringUncons_10)
-- Data.String.Base.tail
d_tail_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_tail_14
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Data.Maybe.Base.du_map_64
         (coe (\ v0 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v0))))
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringUncons_10)
-- Data.String.Base.fromChar
d_fromChar_16 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fromChar_16
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14)
      (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270)
-- Data.String.Base.fromList⁺
d_fromList'8314'_18 ::
  MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fromList'8314'_18
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14)
      (coe MAlonzo.Code.Data.List.NonEmpty.Base.d_toList_60)
-- Data.String.Base._++_
d__'43''43'__20 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d__'43''43'__20
  = coe MAlonzo.Code.Agda.Builtin.String.d_primStringAppend_16
-- Data.String.Base.length
d_length_22 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Integer
d_length_22 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_length_268
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Data.String.Base.replicate
d_replicate_24 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_replicate_24 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
      (coe
         MAlonzo.Code.Data.List.Base.du_replicate_278 (coe v0) (coe v1))
-- Data.String.Base.concat
d_concat_28 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_concat_28
  = coe
      MAlonzo.Code.Data.List.Base.du_foldr_216 (coe d__'43''43'__20)
      (coe ("" :: Data.Text.Text))
-- Data.String.Base.intersperse
d_intersperse_30 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_intersperse_30 v0
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216 (coe d_concat_28)
      (coe MAlonzo.Code.Data.List.Base.du_intersperse_42 (coe v0))
-- Data.String.Base.unwords
d_unwords_34 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_unwords_34 = coe d_intersperse_30 (coe (" " :: Data.Text.Text))
-- Data.String.Base.unlines
d_unlines_36 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_unlines_36 = coe d_intersperse_30 (coe ("\n" :: Data.Text.Text))
-- Data.String.Base.between
d_between_38 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_between_38 v0 v1 v2
  = coe d__'43''43'__20 v0 (coe d__'43''43'__20 v2 v1)
-- Data.String.Base.parens
d_parens_46 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_parens_46
  = coe
      d_between_38 (coe ("(" :: Data.Text.Text))
      (coe (")" :: Data.Text.Text))
-- Data.String.Base.braces
d_braces_48 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_braces_48
  = coe
      d_between_38 (coe ("{" :: Data.Text.Text))
      (coe ("}" :: Data.Text.Text))
-- Data.String.Base._<+>_
d__'60''43''62'__50 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d__'60''43''62'__50 v0 v1
  = let v2
          = let v2
                  = coe
                      d__'43''43'__20 v0
                      (coe d__'43''43'__20 (" " :: Data.Text.Text) v1) in
            coe
              (case coe v1 of
                 l | (==) l ("" :: Data.Text.Text) -> coe v0
                 _ -> coe v2) in
    coe
      (case coe v0 of
         l | (==) l ("" :: Data.Text.Text) -> coe v1
         _ -> coe v2)
-- Data.String.Base.padLeft
d_padLeft_60 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_padLeft_60 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         eqInt
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
            (d_length_22 (coe v2)))
         (coe (0 :: Integer)))
      (coe v2)
      (coe
         d__'43''43'__20
         (d_replicate_24
            (coe
               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
               (d_length_22 (coe v2)))
            (coe v0))
         v2)
-- Data.String.Base.padRight
d_padRight_70 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_padRight_70 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         eqInt
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
            (d_length_22 (coe v2)))
         (coe (0 :: Integer)))
      (coe v2)
      (coe
         d__'43''43'__20 v2
         (d_replicate_24
            (coe
               MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v1
               (d_length_22 (coe v2)))
            (coe v0)))
-- Data.String.Base.padBoth
d_padBoth_80 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_padBoth_80 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         eqInt
         (coe
            MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2
            (d_length_22 (coe v3)))
         (coe (0 :: Integer)))
      (coe v3)
      (coe
         d__'43''43'__20
         (d_replicate_24
            (coe
               MAlonzo.Code.Data.Nat.Base.d_'8970'_'47'2'8971'_268
               (coe
                  MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2
                  (d_length_22 (coe v3))))
            (coe v0))
         (coe
            d__'43''43'__20 v3
            (d_replicate_24
               (coe
                  MAlonzo.Code.Data.Nat.Base.d_'8968'_'47'2'8969'_272
                  (coe
                     MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v2
                     (d_length_22 (coe v3))))
               (coe v1))))
-- Data.String.Base.Alignment
d_Alignment_92 = ()
data T_Alignment_92 = C_Left_94 | C_Center_96 | C_Right_98
-- Data.String.Base.fromAlignment
d_fromAlignment_100 ::
  T_Alignment_92 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_fromAlignment_100 v0
  = case coe v0 of
      C_Left_94 -> coe d_padRight_70 (coe ' ')
      C_Center_96 -> coe d_padBoth_80 (coe ' ') (coe ' ')
      C_Right_98 -> coe d_padLeft_60 (coe ' ')
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.String.Base.wordsBy
d_wordsBy_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_wordsBy_106 ~v0 ~v1 v2 v3 = du_wordsBy_106 v2 v3
du_wordsBy_106 ::
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_wordsBy_106 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14)
      (coe
         MAlonzo.Code.Data.List.Base.du_wordsBy_802 v0
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1))
-- Data.String.Base.wordsByᵇ
d_wordsBy'7495'_110 ::
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_wordsBy'7495'_110 v0
  = coe
      du_wordsBy_106
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
              (coe v0 v1)))
-- Data.String.Base.words
d_words_114 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_words_114
  = coe
      d_wordsBy'7495'_110
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primIsSpace_14)
-- Data.String.Base.linesBy
d_linesBy_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_linesBy_122 ~v0 ~v1 v2 v3 = du_linesBy_122 v2 v3
du_linesBy_122 ::
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
du_linesBy_122 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14)
      (coe
         MAlonzo.Code.Data.List.Base.du_linesBy_770 v0
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1))
-- Data.String.Base.linesByᵇ
d_linesBy'7495'_126 ::
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_linesBy'7495'_126 v0
  = coe
      du_linesBy_122
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
              (coe v0 v1)))
-- Data.String.Base.lines
d_lines_130 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_lines_130
  = coe
      d_linesBy'7495'_126
      (coe MAlonzo.Code.Data.Char.Base.d__'8776''7495'__14 (coe '\n'))
-- Data.String.Base.map
d_map_136 ::
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
   MAlonzo.Code.Agda.Builtin.Char.T_Char_6) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_map_136 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.String.d_primStringFromList_14
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22 (coe v0)
         (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1))
