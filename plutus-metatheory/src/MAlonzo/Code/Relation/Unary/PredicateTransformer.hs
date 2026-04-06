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

module MAlonzo.Code.Relation.Unary.PredicateTransformer where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Relation.Unary.PredicateTransformer.PT
d_PT_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> ()
d_PT_32 = erased
-- Relation.Unary.PredicateTransformer.Pt
d_Pt_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> ()
d_Pt_44 = erased
-- Relation.Unary.PredicateTransformer._⍮_
d__'9070'__50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  (AgdaAny -> ()) -> AgdaAny -> ()
d__'9070'__50 = erased
-- Relation.Unary.PredicateTransformer.skip
d_skip_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) -> AgdaAny -> ()
d_skip_56 = erased
-- Relation.Unary.PredicateTransformer.abort
d_abort_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> AgdaAny -> ()
d_abort_60 = erased
-- Relation.Unary.PredicateTransformer.magic
d_magic_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> AgdaAny -> ()
d_magic_64 = erased
-- Relation.Unary.PredicateTransformer.∼_
d_'8764'__68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  (AgdaAny -> ()) -> AgdaAny -> ()
d_'8764'__68 = erased
-- Relation.Unary.PredicateTransformer._⊑_
d__'8849'__72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) -> ()
d__'8849'__72 = erased
-- Relation.Unary.PredicateTransformer._⊑′_
d__'8849''8242'__80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) -> ()
d__'8849''8242'__80 = erased
-- Relation.Unary.PredicateTransformer._⊒_
d__'8850'__88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) -> ()
d__'8850'__88 = erased
-- Relation.Unary.PredicateTransformer._⊒′_
d__'8850''8242'__94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) -> ()
d__'8850''8242'__94 = erased
-- Relation.Unary.PredicateTransformer._⋢_
d__'8930'__100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) -> ()
d__'8930'__100 = erased
-- Relation.Unary.PredicateTransformer._⊓_
d__'8851'__108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  (AgdaAny -> ()) -> AgdaAny -> ()
d__'8851'__108 = erased
-- Relation.Unary.PredicateTransformer._⊔_
d__'8852'__116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  (AgdaAny -> ()) -> AgdaAny -> ()
d__'8852'__116 = erased
-- Relation.Unary.PredicateTransformer._⇛_
d__'8667'__124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  (AgdaAny -> ()) -> AgdaAny -> ()
d__'8667'__124 = erased
-- Relation.Unary.PredicateTransformer.⨆
d_'10758'_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> (AgdaAny -> ()) -> AgdaAny -> ()) ->
  (AgdaAny -> ()) -> AgdaAny -> ()
d_'10758'_134 = erased
-- Relation.Unary.PredicateTransformer.⨅
d_'10757'_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> (AgdaAny -> ()) -> AgdaAny -> ()) ->
  (AgdaAny -> ()) -> AgdaAny -> ()
d_'10757'_146 = erased
-- Relation.Unary.PredicateTransformer.⟨_⟩
d_'10216'_'10217'_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> ()) -> AgdaAny -> ()
d_'10216'_'10217'_156 = erased
-- Relation.Unary.PredicateTransformer.[_]
d_'91'_'93'_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> ()) -> AgdaAny -> ()
d_'91'_'93'_164 = erased
