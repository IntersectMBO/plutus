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

module MAlonzo.Code.Utils.Reflection where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Char.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Utils.Reflection.constructors
d_constructors_4 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Definition_280 -> [AgdaAny]
d_constructors_4 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'type_290 v2 v3
           -> coe v3
         _ -> coe v1)
-- Utils.Reflection.names
d_names_10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_names_10
  = coe
      MAlonzo.Code.Data.String.Base.du_wordsBy_106
      (coe
         (\ v0 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_66
              (coe
                 MAlonzo.Code.Data.Char.Base.d__'8776''7495'__14 (coe v0)
                 (coe '.'))))
-- Utils.Reflection.lastName
d_lastName_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_lastName_14 v0 v1
  = let v2 = coe MAlonzo.Code.Data.List.Base.du_last_540 (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3 -> coe v3
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.Reflection.getLastName
d_getLastName_34 ::
  AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_getLastName_34 v0
  = coe
      d_lastName_14 (coe ("defconstructorname" :: Data.Text.Text))
      (coe
         d_names_10
         (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12 v0))
-- Utils.Reflection.mk-cls
d_mk'45'cls_38 ::
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160
d_mk'45'cls_38 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
            (coe
               MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
               (coe
                  MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                  (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                  (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
            (coe
               MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 (coe v0)
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
            (coe
               MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
               (coe
                  MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                  (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                  (coe
                     MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                     (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                     (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
               (coe
                  MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 (coe v0)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      (coe
         MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
         (coe
            (MAlonzo.RTE.QName
               (10 :: Integer) (4305008439024043551 :: Integer)
               "Agda.Builtin.Bool.Bool.true"
               (MAlonzo.RTE.Fixity MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Utils.Reflection.wildcard
d_wildcard_42 :: MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88
d_wildcard_42
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
      (coe
         MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
         (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
         (coe
            MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
      (coe
         MAlonzo.Code.Agda.Builtin.Reflection.C_dot_248
         (coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))
-- Utils.Reflection.absurd-lam
d_absurd'45'lam_44 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_absurd'45'lam_44
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Reflection.C_absurd'45'clause_278
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe ("()" :: Data.Text.Text))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                     (coe
                        MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                        (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                        (coe
                           MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                           (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                           (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                     (coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216)))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
               (coe
                  MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                  (coe
                     MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                     (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                        (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                        (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                  (coe
                     MAlonzo.Code.Agda.Builtin.Reflection.C_absurd_264
                     (coe (0 :: Integer))))
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Utils.Reflection.default-cls
d_default'45'cls_46 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160
d_default'45'cls_46
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe d_wildcard_42)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe d_wildcard_42)
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      (coe
         MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
         (coe
            (MAlonzo.RTE.QName
               (8 :: Integer) (4305008439024043551 :: Integer)
               "Agda.Builtin.Bool.Bool.false"
               (MAlonzo.RTE.Fixity MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Utils.Reflection.map2
d_map2_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
d_map2_56 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_map2_56 v4 v5
du_map2_56 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
du_map2_56 v0 v1 = coe du_map2''_70 (coe v0) (coe v1) (coe v1)
-- Utils.Reflection._.map2'
d_map2''_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d_map2''_70 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_map2''_70 v6 v7 v8
du_map2''_70 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du_map2''_70 v0 v1 v2
  = case coe v1 of
      [] -> coe v1
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.List.Base.du__'43''43'__32
             (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v0 v3) (coe v2))
             (coe du_map2''_70 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Reflection.mk-DecCls
d_mk'45'DecCls_82 ::
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160
d_mk'45'DecCls_82 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Agda.Builtin.Reflection.d_primQNameEquality_8 v0 v1 in
    coe
      (if coe v2
         then coe
                MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                      (coe
                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                         (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 (coe v0)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 (coe v1)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
                   (coe
                      (MAlonzo.RTE.QName
                         (32 :: Integer) (16368259409245829246 :: Integer)
                         "Relation.Nullary.Decidable.Core._because_"
                         (MAlonzo.RTE.Fixity
                            MAlonzo.RTE.NonAssoc (MAlonzo.RTE.Related (2.0 :: Double)))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
                            (coe
                               (MAlonzo.RTE.QName
                                  (10 :: Integer) (4305008439024043551 :: Integer)
                                  "Agda.Builtin.Bool.Bool.true"
                                  (MAlonzo.RTE.Fixity MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                            (coe
                               MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                  (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                  (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
                               (coe
                                  (MAlonzo.RTE.QName
                                     (22 :: Integer) (5284306542668000596 :: Integer)
                                     "Relation.Nullary.Reflects.Reflects.of\696"
                                     (MAlonzo.RTE.Fixity
                                        MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
                               (coe
                                  MAlonzo.Code.Data.List.Base.du_'91'_'93'_286
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                        (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                           (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
                                        (coe
                                           (MAlonzo.RTE.QName
                                              (20 :: Integer) (1335258922519917603 :: Integer)
                                              "Agda.Builtin.Equality._\8801_.refl"
                                              (MAlonzo.RTE.Fixity
                                                 MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
                                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
         else coe
                MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                      (coe
                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                         (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 (coe v0)
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 (coe v1)
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                (coe
                   MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
                   (coe
                      (MAlonzo.RTE.QName
                         (32 :: Integer) (16368259409245829246 :: Integer)
                         "Relation.Nullary.Decidable.Core._because_"
                         (MAlonzo.RTE.Fixity
                            MAlonzo.RTE.NonAssoc (MAlonzo.RTE.Related (2.0 :: Double)))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
                            (coe
                               (MAlonzo.RTE.QName
                                  (8 :: Integer) (4305008439024043551 :: Integer)
                                  "Agda.Builtin.Bool.Bool.false"
                                  (MAlonzo.RTE.Fixity MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                            (coe
                               MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                  (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                  (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                            (coe
                               MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
                               (coe
                                  (MAlonzo.RTE.QName
                                     (26 :: Integer) (5284306542668000596 :: Integer)
                                     "Relation.Nullary.Reflects.Reflects.of\8319"
                                     (MAlonzo.RTE.Fixity
                                        MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
                               (coe
                                  MAlonzo.Code.Data.List.Base.du_'91'_'93'_286
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                                        (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                           (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                                     (coe d_absurd'45'lam_44)))))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
-- Utils.Reflection.defEq
d_defEq_100 :: AgdaAny -> AgdaAny -> AgdaAny
d_defEq_100 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
      erased
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_getDefinition_408 v0)
      (\ v2 ->
         coe
           MAlonzo.Code.Agda.Builtin.Reflection.d_defineFun_404 v1
           (coe
              MAlonzo.Code.Data.List.Base.du__'43''43'__32
              (coe
                 MAlonzo.Code.Data.List.Base.du_map_22 (coe d_mk'45'cls_38)
                 (coe d_constructors_4 (coe v2)))
              (coe
                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                 (coe d_default'45'cls_46)
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Utils.Reflection.defDec
d_defDec_110 :: AgdaAny -> AgdaAny -> AgdaAny
d_defDec_110 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
      erased
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_getDefinition_408 v0)
      (\ v2 ->
         coe
           MAlonzo.Code.Agda.Builtin.Reflection.d_defineFun_404 v1
           (coe
              du_map2_56 (coe d_mk'45'DecCls_82)
              (coe d_constructors_4 (coe v2))))
-- Utils.Reflection.mk-Show
d_mk'45'Show_120 ::
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160
d_mk'45'Show_120 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
            (coe
               MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
               (coe
                  MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                  (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                  (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
            (coe
               MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 (coe v0)
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
      (coe
         MAlonzo.Code.Agda.Builtin.Reflection.C_lit_210
         (coe
            MAlonzo.Code.Agda.Builtin.Reflection.C_string_144
            (coe d_getLastName_34 (coe v0))))
-- Utils.Reflection.defShow
d_defShow_124 :: AgdaAny -> AgdaAny -> AgdaAny
d_defShow_124 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
      erased
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_getDefinition_408 v0)
      (\ v2 ->
         coe
           MAlonzo.Code.Agda.Builtin.Reflection.d_defineFun_404 v1
           (coe
              MAlonzo.Code.Data.List.Base.du_map_22 (coe d_mk'45'Show_120)
              (coe d_constructors_4 (coe v2))))
-- Utils.Reflection.mkList
d_mkList_134 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_mkList_134 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
             (coe
                (MAlonzo.RTE.QName
                   (16 :: Integer) (15090436609435731260 :: Integer)
                   "Agda.Builtin.List.List.[]"
                   (MAlonzo.RTE.Fixity MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
             (coe v0)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
             (coe
                (MAlonzo.RTE.QName
                   (22 :: Integer) (15090436609435731260 :: Integer)
                   "Agda.Builtin.List.List._\8759_"
                   (MAlonzo.RTE.Fixity
                      MAlonzo.RTE.RightAssoc (MAlonzo.RTE.Related (5.0 :: Double)))))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                   (coe
                      MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_hidden_52)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                         (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                         (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                   (coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                   (coe
                      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                      (coe
                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                         (coe MAlonzo.Code.Agda.Builtin.Reflection.C_hidden_52)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                      (coe
                         MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                            (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                         (coe v1))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                         (coe
                            MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98
                            (coe
                               MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82
                               (coe MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74
                                  (coe MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58)
                                  (coe MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66)))
                            (coe d_mkList_134 (coe v2)))
                         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Reflection.defListConstructors
d_defListConstructors_140 :: AgdaAny -> AgdaAny -> AgdaAny
d_defListConstructors_140 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () () erased
      erased
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_getDefinition_408 v0)
      (\ v2 ->
         coe
           MAlonzo.Code.Agda.Builtin.Reflection.d_defineFun_404 v1
           (coe
              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
              (coe
                 MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                 (coe
                    d_mkList_134
                    (coe
                       MAlonzo.Code.Data.List.Base.du_map_22
                       (coe
                          (\ v3 ->
                             coe
                               MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 (coe v3)
                               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
                       (coe d_constructors_4 (coe v2)))))
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
