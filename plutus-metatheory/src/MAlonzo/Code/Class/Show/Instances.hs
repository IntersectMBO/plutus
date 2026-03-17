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

module MAlonzo.Code.Class.Show.Instances where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Show.Core
import qualified MAlonzo.Code.Data.Bool.Show
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.Rational.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Reflection.AST.Show

-- Class.Show.Instances.Show-×
d_Show'45''215'_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45''215'_6 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_Show'45''215'_6 v4 v5
du_Show'45''215'_6 ::
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  MAlonzo.Code.Class.Show.Core.T_Show_10
du_Show'45''215'_6 v0 v1
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe
         (\ v2 ->
            case coe v2 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                -> coe
                     MAlonzo.Code.Data.String.Base.d_parens_46
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20
                        (coe MAlonzo.Code.Class.Show.Core.d_show_16 v0 v3)
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (" , " :: Data.Text.Text)
                           (coe MAlonzo.Code.Class.Show.Core.d_show_16 v1 v4)))
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.Show.Instances.Show-Maybe
d_Show'45'Maybe_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Maybe_12 ~v0 ~v1 v2 = du_Show'45'Maybe_12 v2
du_Show'45'Maybe_12 ::
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  MAlonzo.Code.Class.Show.Core.T_Show_10
du_Show'45'Maybe_12 v0
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe
         (\ v1 ->
            case coe v1 of
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                -> coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     ("just " :: Data.Text.Text)
                     (coe MAlonzo.Code.Class.Show.Core.d_show_16 v0 v2)
              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                -> coe ("nothing" :: Data.Text.Text)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.Show.Instances.Show-List
d_Show'45'List_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'List_16 ~v0 ~v1 v2 = du_Show'45'List_16 v2
du_Show'45'List_16 ::
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  MAlonzo.Code.Class.Show.Core.T_Show_10
du_Show'45'List_16 v0
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Data.String.Base.d_braces_48
              (coe
                 MAlonzo.Code.Data.String.Base.d_intersperse_30
                 (", " :: Data.Text.Text)
                 (coe
                    MAlonzo.Code.Data.List.Base.du_map_22
                    (coe MAlonzo.Code.Class.Show.Core.d_show_16 (coe v0)) (coe v1)))))
-- Class.Show.Instances.Show-String
d_Show'45'String_18 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'String_18
  = coe MAlonzo.Code.Class.Show.Core.C_mkShow_18 (coe (\ v0 -> v0))
-- Class.Show.Instances.Show-⊤
d_Show'45''8868'_20 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45''8868'_20
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe (\ v0 -> seq (coe v0) (coe ("tt" :: Data.Text.Text))))
-- Class.Show.Instances.Show-Char
d_Show'45'Char_24 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Char_24
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Agda.Builtin.String.d_primShowChar_20)
-- Class.Show.Instances.Show-Bool
d_Show'45'Bool_30 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Bool_30
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Data.Bool.Show.d_show_6)
-- Class.Show.Instances.Show-ℕ
d_Show'45'ℕ_36 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'ℕ_36
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56)
-- Class.Show.Instances.Show-ℤ
d_Show'45'ℤ_42 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'ℤ_42
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Data.Integer.Show.d_show_6)
-- Class.Show.Instances.Show-ℚ
d_Show'45'ℚ_48 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'ℚ_48
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Data.Rational.Show.d_show_6)
-- Class.Show.Instances.Show-Fin
d_Show'45'Fin_54 ::
  Integer -> MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Fin_54 ~v0 = du_Show'45'Fin_54
du_Show'45'Fin_54 :: MAlonzo.Code.Class.Show.Core.T_Show_10
du_Show'45'Fin_54
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Data.String.Base.d__'43''43'__20
              ("# " :: Data.Text.Text)
              (coe
                 MAlonzo.Code.Class.Show.Core.d_show_16 d_Show'45'ℕ_36
                 (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v0)))))
-- Class.Show.Instances.Show-Float
d_Show'45'Float_62 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Float_62
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Agda.Builtin.Float.d_primShowFloat_46)
-- Class.Show.Instances.Show-Name
d_Show'45'Name_68 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Name_68
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12)
-- Class.Show.Instances.Show-Meta
d_Show'45'Meta_70 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Meta_70
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowMeta_44)
-- Class.Show.Instances.Show-Relevance
d_Show'45'Relevance_72 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Relevance_72
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Reflection.AST.Show.d_showRel_8)
-- Class.Show.Instances.Show-Vis
d_Show'45'Vis_74 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Vis_74
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Reflection.AST.Show.d_showVisibility_10)
-- Class.Show.Instances.Show-Literal
d_Show'45'Literal_76 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Literal_76
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Reflection.AST.Show.d_showLiteral_14)
-- Class.Show.Instances.Show-Arg
d_Show'45'Arg_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Arg_78 ~v0 ~v1 v2 = du_Show'45'Arg_78 v2
du_Show'45'Arg_78 ::
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  MAlonzo.Code.Class.Show.Core.T_Show_10
du_Show'45'Arg_78 v0
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe
         (\ v1 ->
            case coe v1 of
              MAlonzo.Code.Agda.Builtin.Reflection.C_arg_98 v2 v3
                -> case coe v2 of
                     MAlonzo.Code.Agda.Builtin.Reflection.C_arg'45'info_82 v4 v5
                       -> coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (MAlonzo.Code.Reflection.AST.Show.d_showVisibility_10 (coe v4))
                            (coe MAlonzo.Code.Class.Show.Core.d_show_16 v0 v3)
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.Show.Instances.Show-Abs
d_Show'45'Abs_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Abs_84 ~v0 ~v1 v2 = du_Show'45'Abs_84 v2
du_Show'45'Abs_84 ::
  MAlonzo.Code.Class.Show.Core.T_Show_10 ->
  MAlonzo.Code.Class.Show.Core.T_Show_10
du_Show'45'Abs_84 v0
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe
         (\ v1 ->
            case coe v1 of
              MAlonzo.Code.Agda.Builtin.Reflection.C_abs_122 v2 v3
                -> coe
                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                     ("abs " :: Data.Text.Text)
                     (coe
                        MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                        (coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           (" " :: Data.Text.Text)
                           (coe MAlonzo.Code.Class.Show.Core.d_show_16 v0 v3)))
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.Show.Instances.Show-Names
d_Show'45'Names_90 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Names_90
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Reflection.AST.Show.d_showTerms_38)
-- Class.Show.Instances.Show-Term
d_Show'45'Term_92 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Term_92
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Reflection.AST.Show.d_showTerm_40)
-- Class.Show.Instances.Show-Sort
d_Show'45'Sort_94 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Sort_94
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Reflection.AST.Show.d_showSort_42)
-- Class.Show.Instances.Show-Patterns
d_Show'45'Patterns_96 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Patterns_96
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Reflection.AST.Show.d_showPatterns_44)
-- Class.Show.Instances.Show-Pattern
d_Show'45'Pattern_98 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Pattern_98
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Reflection.AST.Show.d_showPattern_46)
-- Class.Show.Instances.Show-Clause
d_Show'45'Clause_100 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Clause_100
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Reflection.AST.Show.d_showClause_48)
-- Class.Show.Instances.Show-Clauses
d_Show'45'Clauses_102 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Clauses_102
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Reflection.AST.Show.d_showClauses_50)
-- Class.Show.Instances.Show-Tel
d_Show'45'Tel_104 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Tel_104
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Reflection.AST.Show.d_showTel_52)
-- Class.Show.Instances.Show-Definition
d_Show'45'Definition_106 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'Definition_106
  = coe
      MAlonzo.Code.Class.Show.Core.C_mkShow_18
      (coe MAlonzo.Code.Reflection.AST.Show.d_showDefinition_168)
-- Class.Show.Instances.Show-AName
d_Show'45'AName_108 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'AName_108
  = coe
      du_Show'45'Arg_78
      (coe
         MAlonzo.Code.Class.Show.Core.C_mkShow_18
         (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12))
-- Class.Show.Instances.Show-AType
d_Show'45'AType_110 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'AType_110
  = coe
      du_Show'45'Arg_78
      (coe
         MAlonzo.Code.Class.Show.Core.C_mkShow_18
         (coe MAlonzo.Code.Reflection.AST.Show.d_showTerm_40))
-- Class.Show.Instances.Show-ATerms
d_Show'45'ATerms_112 :: MAlonzo.Code.Class.Show.Core.T_Show_10
d_Show'45'ATerms_112
  = coe
      du_Show'45'List_16
      (coe
         du_Show'45'Arg_78
         (coe
            MAlonzo.Code.Class.Show.Core.C_mkShow_18
            (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primShowQName_12)))
