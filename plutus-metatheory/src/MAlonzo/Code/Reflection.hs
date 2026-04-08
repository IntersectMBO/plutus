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

module MAlonzo.Code.Reflection where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Reflection.AST.Abstraction
import qualified MAlonzo.Code.Reflection.AST.Argument
import qualified MAlonzo.Code.Reflection.AST.Argument.Information
import qualified MAlonzo.Code.Reflection.AST.Argument.Modality
import qualified MAlonzo.Code.Reflection.AST.Argument.Relevance
import qualified MAlonzo.Code.Reflection.AST.Argument.Visibility
import qualified MAlonzo.Code.Reflection.AST.Literal
import qualified MAlonzo.Code.Reflection.AST.Meta
import qualified MAlonzo.Code.Reflection.AST.Name
import qualified MAlonzo.Code.Reflection.AST.Term
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Reflection.Arg-info
d_Arg'45'info_2 :: ()
d_Arg'45'info_2 = erased
-- Reflection._≟-Lit_
d__'8799''45'Lit__4 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Literal_124 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Literal_124 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'Lit__4
  = coe MAlonzo.Code.Reflection.AST.Literal.d__'8799'__48
-- Reflection._≟-Name_
d__'8799''45'Name__6 ::
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'Name__6
  = coe MAlonzo.Code.Reflection.AST.Name.d__'8799'__12
-- Reflection._≟-Meta_
d__'8799''45'Meta__8 ::
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'Meta__8
  = coe MAlonzo.Code.Reflection.AST.Meta.d__'8799'__10
-- Reflection._≟-Visibility_
d__'8799''45'Visibility__10 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'Visibility__10
  = coe MAlonzo.Code.Reflection.AST.Argument.Visibility.d__'8799'__8
-- Reflection._≟-Relevance_
d__'8799''45'Relevance__12 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Relevance_56 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Relevance_56 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'Relevance__12
  = coe MAlonzo.Code.Reflection.AST.Argument.Relevance.d__'8799'__8
-- Reflection._≟-Arg-info_
d__'8799''45'Arg'45'info__14 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_ArgInfo_76 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_ArgInfo_76 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'Arg'45'info__14
  = coe
      MAlonzo.Code.Reflection.AST.Argument.Information.d__'8799'__30
-- Reflection._≟-Pattern_
d__'8799''45'Pattern__16 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Pattern_158 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'Pattern__16
  = coe MAlonzo.Code.Reflection.AST.Term.d__'8799''45'Pattern__230
-- Reflection._≟-ArgPatterns_
d__'8799''45'ArgPatterns__18 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'ArgPatterns__18
  = coe MAlonzo.Code.Reflection.AST.Term.d__'8799''45'Patterns__228
-- Reflection.map-Abs
d_map'45'Abs_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112
d_map'45'Abs_20 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Reflection.AST.Abstraction.du_map_22 v4 v5
-- Reflection.map-Arg
d_map'45'Arg_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88
d_map'45'Arg_22 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Reflection.AST.Argument.du_map_54 v4 v5
-- Reflection.map-Args
d_map'45'Args_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88]
d_map'45'Args_24 v0 v1 v2 v3 v4 v5
  = coe MAlonzo.Code.Reflection.AST.Argument.du_map'45'Args_62 v4 v5
-- Reflection.visibility
d_visibility_26 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_ArgInfo_76 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Visibility_48
d_visibility_26
  = coe
      MAlonzo.Code.Reflection.AST.Argument.Information.d_visibility_16
-- Reflection.relevance
d_relevance_28 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Modality_68 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Relevance_56
d_relevance_28
  = coe MAlonzo.Code.Reflection.AST.Argument.Modality.d_relevance_16
-- Reflection._≟-AbsTerm_
d__'8799''45'AbsTerm__30 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'AbsTerm__30
  = coe MAlonzo.Code.Reflection.AST.Term.d__'8799''45'AbsTerm__210
-- Reflection._≟-AbsType_
d__'8799''45'AbsType__32 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Abs_112 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'AbsType__32
  = coe MAlonzo.Code.Reflection.AST.Term.d__'8799''45'AbsType__212
-- Reflection._≟-ArgTerm_
d__'8799''45'ArgTerm__34 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'ArgTerm__34
  = coe MAlonzo.Code.Reflection.AST.Term.d__'8799''45'ArgTerm__214
-- Reflection._≟-ArgType_
d__'8799''45'ArgType__36 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'ArgType__36
  = coe MAlonzo.Code.Reflection.AST.Term.d__'8799''45'ArgType__216
-- Reflection._≟-Args_
d__'8799''45'Args__38 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Arg_88] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'Args__38
  = coe MAlonzo.Code.Reflection.AST.Term.d__'8799''45'Args__218
-- Reflection._≟-Clause_
d__'8799''45'Clause__40 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'Clause__40
  = coe MAlonzo.Code.Reflection.AST.Term.d__'8799''45'Clause__220
-- Reflection._≟-Clauses_
d__'8799''45'Clauses__42 ::
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_Clause_160] ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'Clauses__42
  = coe MAlonzo.Code.Reflection.AST.Term.d__'8799''45'Clauses__222
-- Reflection._≟_
d__'8799'__44 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Term_154 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__44 = coe MAlonzo.Code.Reflection.AST.Term.d__'8799'__224
-- Reflection._≟-Sort_
d__'8799''45'Sort__46 ::
  MAlonzo.Code.Agda.Builtin.Reflection.T_Sort_156 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_Sort_156 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''45'Sort__46
  = coe MAlonzo.Code.Reflection.AST.Term.d__'8799''45'Sort__226
