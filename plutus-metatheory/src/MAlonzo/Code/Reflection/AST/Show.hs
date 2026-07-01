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

module MAlonzo.Code.Reflection.AST.Show where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Reflection.AST.Argument
import qualified MAlonzo.Code.Reflection.AST.Argument.Information

-- Reflection.AST.Show.showRelevance
d_showRelevance_6 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Relevance_56 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showRelevance_6 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58
        -> coe ("relevant" :: Data.Text.Text)
      MAlonzo.Code.Agda.Builtin.Reflection.C_irrelevant_60
        -> coe ("irrelevant" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show.showRel
d_showRel_8 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Relevance_56 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showRel_8 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_relevant_58
        -> coe ("" :: Data.Text.Text)
      MAlonzo.Code.Agda.Builtin.Reflection.C_irrelevant_60
        -> coe ("." :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show.showVisibility
d_showVisibility_10 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showVisibility_10 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50
        -> coe ("visible" :: Data.Text.Text)
      MAlonzo.Code.Agda.Builtin.Reflection.C_hidden_52
        -> coe ("hidden" :: Data.Text.Text)
      MAlonzo.Code.Agda.Builtin.Reflection.C_instance'8242'_54
        -> coe ("instance" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show.showQuantity
d_showQuantity_12 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showQuantity_12 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'0_64
        -> coe ("quantity-0" :: Data.Text.Text)
      MAlonzo.Code.Agda.Builtin.Reflection.C_quantity'45'ω_66
        -> coe ("quantity-\969" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show.showLiteral
d_showLiteral_14 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Literal_124 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showLiteral_14 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_nat_128 v1
        -> coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1
      MAlonzo.Code.Agda.Builtin.Reflection.C_word64_132 v1
        -> coe MAlonzo.Code.Data.Nat.Show.d_show_56 (word64ToNat (coe v1))
      MAlonzo.Code.Agda.Builtin.Reflection.C_float_136 v1
        -> coe MAlonzo.Code.Agda.Builtin.Float.d_primShowFloat_46 v1
      MAlonzo.Code.Agda.Builtin.Reflection.C_char_140 v1
        -> coe MAlonzo.Code.Agda.Builtin.String.d_primShowChar_20 v1
      MAlonzo.Code.Agda.Builtin.Reflection.C_string_144 v1
        -> coe MAlonzo.Code.Agda.Builtin.String.d_primShowString_22 v1
      MAlonzo.Code.Agda.Builtin.Reflection.C_name_148 v1
        -> coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12 v1
      MAlonzo.Code.Agda.Builtin.Reflection.C_meta_152 v1
        -> coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowMeta_44 v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show.visibilityParen
d_visibilityParen_30 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_visibilityParen_30 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50
        -> coe MAlonzo.Code.Data.String.d_parensIfSpace_130 (coe v1)
      MAlonzo.Code.Agda.Builtin.Reflection.C_hidden_52
        -> coe MAlonzo.Code.Data.String.Base.d_braces_48 v1
      MAlonzo.Code.Agda.Builtin.Reflection.C_instance'8242'_54
        -> coe
             MAlonzo.Code.Data.String.Base.d_braces_48
             (coe MAlonzo.Code.Data.String.Base.d_braces_48 v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show.showTerms
d_showTerms_38 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showTerms_38 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v3 v4
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                    (coe
                       d_visibilityParen_30
                       (coe
                          MAlonzo.Code.Reflection.AST.Argument.Information.d_visibility_16
                          (coe v3))
                       (coe d_showTerm_40 (coe v4)))
                    (coe d_showTerms_38 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show.showTerm
d_showTerm_40 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showTerm_40 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_var_172 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe ("var" :: Data.Text.Text))
             (coe
                MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                (coe d_showTerms_38 (coe v2)))
      MAlonzo.Code.Agda.Builtin.Reflection.C_con_178 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12 v1)
             (coe d_showTerms_38 (coe v2))
      MAlonzo.Code.Agda.Builtin.Reflection.C_def_184 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12 v1)
             (coe d_showTerms_38 (coe v2))
      MAlonzo.Code.Agda.Builtin.Reflection.C_lam_190 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v3 v4
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                    (coe ("\955" :: Data.Text.Text))
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                       (coe d_visibilityParen_30 (coe v1) (coe v3))
                       (coe
                          MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                          (coe ("\8594" :: Data.Text.Text)) (coe d_showTerm_40 (coe v4))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe ("\955 {" :: Data.Text.Text))
             (coe
                MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                (coe d_showClauses_50 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                   (coe ("}" :: Data.Text.Text)) (coe d_showTerms_38 (coe v2))))
      MAlonzo.Code.Agda.Builtin.Reflection.C_pi_202 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v3 v4
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v5 v6
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("\928 (" :: Data.Text.Text)
                           (MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                              (coe
                                 d_visibilityParen_30
                                 (coe
                                    MAlonzo.Code.Reflection.AST.Argument.Information.d_visibility_16
                                    (coe v3))
                                 (coe v5))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                                 (coe (":" :: Data.Text.Text))
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (MAlonzo.Code.Data.String.d_parensIfSpace_130
                                       (coe d_showTerm_40 (coe v4)))
                                    (MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                                       (coe (")" :: Data.Text.Text))
                                       (coe
                                          MAlonzo.Code.Data.String.d_parensIfSpace_130
                                          (coe d_showTerm_40 (coe v6)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Reflection.C_agda'45'sort_206 v1
        -> coe d_showSort_42 (coe v1)
      MAlonzo.Code.Agda.Builtin.Reflection.C_lit_210 v1
        -> coe d_showLiteral_14 (coe v1)
      MAlonzo.Code.Agda.Builtin.Reflection.C_meta_214 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowMeta_44 v1)
             (coe d_showTerms_38 (coe v2))
      MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_216
        -> coe ("unknown" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show.showSort
d_showSort_42 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Sort_156 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showSort_42 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_set_220 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe ("Set" :: Data.Text.Text))
             (coe
                MAlonzo.Code.Data.String.d_parensIfSpace_130
                (coe d_showTerm_40 (coe v1)))
      MAlonzo.Code.Agda.Builtin.Reflection.C_lit_224 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Set" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Agda.Builtin.Reflection.C_prop_228 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe ("Prop" :: Data.Text.Text))
             (coe
                MAlonzo.Code.Data.String.d_parensIfSpace_130
                (coe d_showTerm_40 (coe v1)))
      MAlonzo.Code.Agda.Builtin.Reflection.C_propLit_232 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Prop" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Agda.Builtin.Reflection.C_inf_236 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("Set\969" :: Data.Text.Text)
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Agda.Builtin.Reflection.C_unknown_238
        -> coe ("unknown" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show.showPatterns
d_showPatterns_44 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPatterns_44 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe du_showArg_116 (coe v1)) (coe d_showPatterns_44 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show.showPattern
d_showPattern_46 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showPattern_46 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_con_244 v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Data.String.Base.d_parens_46
                     (MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                        (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12 v1)
                        (coe d_showPatterns_44 (coe v2))) in
           coe
             (case coe v2 of
                []
                  -> coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12 v1
                _ -> coe v3)
      MAlonzo.Code.Agda.Builtin.Reflection.C_dot_248 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("." :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d_parens_46 (d_showTerm_40 (coe v1)))
      MAlonzo.Code.Agda.Builtin.Reflection.C_var_252 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe ("pat-var" :: Data.Text.Text))
             (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
      MAlonzo.Code.Agda.Builtin.Reflection.C_lit_256 v1
        -> coe d_showLiteral_14 (coe v1)
      MAlonzo.Code.Agda.Builtin.Reflection.C_proj_260 v1
        -> coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12 v1
      MAlonzo.Code.Agda.Builtin.Reflection.C_absurd_264 v1
        -> coe ("()" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show.showClause
d_showClause_48 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showClause_48 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_clause_272 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe ("[" :: Data.Text.Text))
             (coe
                MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                (coe d_showTel_52 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                   (coe ("]" :: Data.Text.Text))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                      (coe d_showPatterns_44 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                         (coe ("\8594" :: Data.Text.Text)) (coe d_showTerm_40 (coe v3))))))
      MAlonzo.Code.Agda.Builtin.Reflection.C_absurd'45'clause_278 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe ("[" :: Data.Text.Text))
             (coe
                MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                (coe d_showTel_52 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                   (coe ("]" :: Data.Text.Text)) (coe d_showPatterns_44 (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show.showClauses
d_showClauses_50 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showClauses_50 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe d_showClause_48 (coe v1))
             (coe
                MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                (coe (";" :: Data.Text.Text)) (coe d_showClauses_50 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show.showTel
d_showTel_52 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showTel_52 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v5 v6
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (d_visibilityParen_30
                              (coe
                                 MAlonzo.Code.Reflection.AST.Argument.Information.d_visibility_16
                                 (coe v5))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'60''43''62'__50 (coe v3)
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                                    (coe (":" :: Data.Text.Text)) (coe d_showTerm_40 (coe v6)))))
                           (d_showTel_52 (coe v2))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show._.showArg
d_showArg_116 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showArg_116 ~v0 ~v1 v2 = du_showArg_116 v2
du_showArg_116 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_showArg_116 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Reflection.C_modality_74 v5 v6
                      -> coe
                           du_braces'63'_128 v3
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_showRel_8 (coe v5)) (d_showPattern_46 (coe v2)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show._._.braces?
d_braces'63'_128 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Relevance_56 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Quantity_62 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_braces'63'_128 ~v0 ~v1 v2 ~v3 ~v4 ~v5 = du_braces'63'_128 v2
du_braces'63'_128 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
du_braces'63'_128 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_visible_50
        -> coe (\ v1 -> v1)
      MAlonzo.Code.Agda.Builtin.Reflection.C_hidden_52
        -> coe MAlonzo.Code.Data.String.Base.d_braces_48
      MAlonzo.Code.Agda.Builtin.Reflection.C_instance'8242'_54
        -> coe
             MAlonzo.Code.Function.Base.du__'8728''8242'__216
             (coe MAlonzo.Code.Data.String.Base.d_braces_48)
             (coe MAlonzo.Code.Data.String.Base.d_braces_48)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.AST.Show.showDefinition
d_showDefinition_168 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Definition_280 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showDefinition_168 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Reflection.C_function_284 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe ("function" :: Data.Text.Text))
             (coe
                MAlonzo.Code.Data.String.Base.d_braces_48
                (d_showClauses_50 (coe v1)))
      MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'type_290 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe ("datatype" :: Data.Text.Text))
             (coe
                MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                (coe
                   MAlonzo.Code.Data.String.Base.d_braces_48
                   (coe
                      MAlonzo.Code.Data.String.Base.d_intersperse_30
                      (", " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.List.Base.du_map_22
                         (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12)
                         (coe v2)))))
      MAlonzo.Code.Agda.Builtin.Reflection.C_record'45'type_296 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe ("record" :: Data.Text.Text))
             (coe
                MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12 v1)
                (coe
                   MAlonzo.Code.Data.String.Base.d_braces_48
                   (coe
                      MAlonzo.Code.Data.String.Base.d_intersperse_30
                      (", " :: Data.Text.Text)
                      (coe
                         MAlonzo.Code.Data.List.Base.du_map_22
                         (coe
                            MAlonzo.Code.Function.Base.du__'8728''8242'__216
                            (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12)
                            (coe MAlonzo.Code.Reflection.AST.Argument.d_unArg_74))
                         (coe v2)))))
      MAlonzo.Code.Agda.Builtin.Reflection.C_data'45'cons_302 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
             (coe ("constructor" :: Data.Text.Text))
             (coe
                MAlonzo.Code.Data.String.Base.d__'60''43''62'__50
                (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12 v1)
                (coe d_showQuantity_12 (coe v2)))
      MAlonzo.Code.Agda.Builtin.Reflection.C_axiom_304
        -> coe ("axiom" :: Data.Text.Text)
      MAlonzo.Code.Agda.Builtin.Reflection.C_prim'45'fun_306
        -> coe ("primitive" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
