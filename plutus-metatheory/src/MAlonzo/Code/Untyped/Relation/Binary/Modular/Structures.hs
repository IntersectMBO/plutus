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

module MAlonzo.Code.Untyped.Relation.Binary.Modular.Structures where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Relation.Binary.Modular
import qualified MAlonzo.Code.Untyped.Relation.Binary.Structures

-- Untyped.Relation.Binary.Modular.Structures.CompatTerm-TermCompatible
d_CompatTerm'45'TermCompatible_12 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.Relation.Binary.Modular.T__'8853'__16 ->
   AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.Binary.Structures.T_TermCompatible_30
d_CompatTerm'45'TermCompatible_12 ~v0 v1
  = du_CompatTerm'45'TermCompatible_12 v1
du_CompatTerm'45'TermCompatible_12 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.Relation.Binary.Modular.T__'8853'__16 ->
   AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.Binary.Structures.T_TermCompatible_30
du_CompatTerm'45'TermCompatible_12 v0
  = coe
      MAlonzo.Code.Untyped.Relation.Binary.Structures.C_constructor_150
      (coe
         (\ v1 v2 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_'96'_18 (coe v2))
              (coe MAlonzo.Code.Untyped.C_'96'_18 (coe v2))
              (coe
                 MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30
                 (coe MAlonzo.Code.Untyped.Relation.Binary.Modular.C_'96'F__118))))
      (coe
         (\ v1 v2 v3 v4 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_ƛ_20 (coe v2))
              (coe MAlonzo.Code.Untyped.C_ƛ_20 (coe v3))
              (coe
                 MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                 (coe
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30
                    (coe MAlonzo.Code.Untyped.Relation.Binary.Modular.C_ƛF_132 v4)))))
      (coe
         (\ v1 v2 v3 v4 v5 v6 v7 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C__'183'__22 (coe v2) (coe v4))
              (coe MAlonzo.Code.Untyped.C__'183'__22 (coe v3) (coe v5))
              (coe
                 MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                 (coe
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                    (coe
                       MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30
                       (coe
                          MAlonzo.Code.Untyped.Relation.Binary.Modular.C__'183'F__150 v6
                          v7))))))
      (coe
         (\ v1 v2 v3 v4 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_force_24 (coe v2))
              (coe MAlonzo.Code.Untyped.C_force_24 (coe v3))
              (coe
                 MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                 (coe
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                    (coe
                       MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                       (coe
                          MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30
                          (coe
                             MAlonzo.Code.Untyped.Relation.Binary.Modular.C_forceF_164 v4)))))))
      (coe
         (\ v1 v2 v3 v4 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_delay_26 (coe v2))
              (coe MAlonzo.Code.Untyped.C_delay_26 (coe v3))
              (coe
                 MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                 (coe
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                    (coe
                       MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                       (coe
                          MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                          (coe
                             MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30
                             (coe
                                MAlonzo.Code.Untyped.Relation.Binary.Modular.C_delayF_178
                                v4))))))))
      (coe
         (\ v1 v2 v3 v4 v5 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_constr_34 (coe v2) (coe v3))
              (coe MAlonzo.Code.Untyped.C_constr_34 (coe v2) (coe v4))
              (coe
                 MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                 (coe
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                    (coe
                       MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                       (coe
                          MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                          (coe
                             MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                             (coe
                                MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                                (coe
                                   MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30
                                   (coe
                                      MAlonzo.Code.Untyped.Relation.Binary.Modular.C_constrF_206
                                      v5))))))))))
      (coe
         (\ v1 v2 v3 v4 v5 v6 v7 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_case_40 (coe v2) (coe v4))
              (coe MAlonzo.Code.Untyped.C_case_40 (coe v3) (coe v5))
              (coe
                 MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                 (coe
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                    (coe
                       MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                       (coe
                          MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                          (coe
                             MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                             (coe
                                MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                                (coe
                                   MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                                   (coe
                                      MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30
                                      (coe
                                         MAlonzo.Code.Untyped.Relation.Binary.Modular.C_caseF_224 v6
                                         v7)))))))))))
      (coe
         (\ v1 v2 ->
            coe
              v0 v2 (coe MAlonzo.Code.Untyped.C_con_28 (coe v1))
              (coe MAlonzo.Code.Untyped.C_con_28 (coe v1))
              (coe
                 MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                 (coe
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                    (coe
                       MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                       (coe
                          MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                          (coe
                             MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                             (coe
                                MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30
                                (coe
                                   MAlonzo.Code.Untyped.Relation.Binary.Modular.C_conF_190)))))))))
      (coe
         (\ v1 v2 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_builtin_44 (coe v2))
              (coe MAlonzo.Code.Untyped.C_builtin_44 (coe v2))
              (coe
                 MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                 (coe
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                    (coe
                       MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                       (coe
                          MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                          (coe
                             MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                             (coe
                                MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                                (coe
                                   MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                                   (coe
                                      MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                                      (coe
                                         MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30
                                         (coe
                                            MAlonzo.Code.Untyped.Relation.Binary.Modular.C_builtinF_236))))))))))))
      (coe
         (\ v1 ->
            coe
              v0 v1 (coe MAlonzo.Code.Untyped.C_error_46)
              (coe MAlonzo.Code.Untyped.C_error_46)
              (coe
                 MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                 (coe
                    MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                    (coe
                       MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                       (coe
                          MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                          (coe
                             MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                             (coe
                                MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                                (coe
                                   MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                                   (coe
                                      MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                                      (coe
                                         MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inr_38
                                         (coe
                                            MAlonzo.Code.Untyped.Relation.Binary.Modular.C_inl_30
                                            (coe
                                               MAlonzo.Code.Untyped.Relation.Binary.Modular.C_errorF_246)))))))))))))
