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

module MAlonzo.Code.Reflection.QQuotedDefinitions where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Reflection

-- Reflection.QuotedDefinitions._`≡_
d__'96''8801'__4 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d__'96''8801'__4 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_def_184
      (coe
         (MAlonzo.RTE.QName
            (12 :: Integer) (1335258922519917603 :: Integer)
            "Agda.Builtin.Equality._\8801_"
            (MAlonzo.RTE.Fixity
               MAlonzo.RTE.NonAssoc (MAlonzo.RTE.Related (4.0 :: Double)))))
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
            (coe v0))
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
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Reflection.QuotedDefinitions.`refl
d_'96'refl_16 :: MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_'96'refl_16
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_con_178
      (coe
         (MAlonzo.RTE.QName
            (20 :: Integer) (1335258922519917603 :: Integer)
            "Agda.Builtin.Equality._\8801_.refl"
            (MAlonzo.RTE.Fixity MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Reflection.QuotedDefinitions.`case_of_
d_'96'case_of__20 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_'96'case_of__20 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_def_184
      (coe
         (MAlonzo.RTE.QName
            (234 :: Integer) (10779521135412943468 :: Integer)
            "Function.Base.case_of_"
            (MAlonzo.RTE.Fixity
               MAlonzo.RTE.NonAssoc (MAlonzo.RTE.Related (0.0 :: Double)))))
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
            (coe v0))
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
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Reflection.QuotedDefinitions.`yes
d_'96'yes_26 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_'96'yes_26 v0
  = coe
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
                        (MAlonzo.RTE.Fixity MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
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
                        (coe v0))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
-- Reflection.QuotedDefinitions.`no
d_'96'no_28 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154
d_'96'no_28 v0
  = coe
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
                        (MAlonzo.RTE.Fixity MAlonzo.RTE.NonAssoc MAlonzo.RTE.Unrelated)))
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
                        (coe v0))
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
