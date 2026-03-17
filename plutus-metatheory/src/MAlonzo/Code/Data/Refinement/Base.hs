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

module MAlonzo.Code.Data.Refinement.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant

-- Data.Refinement.Base.Refinement
d_Refinement_28 a0 a1 a2 a3 = ()
newtype T_Refinement_28 = C__'44'__42 AgdaAny
-- Data.Refinement.Base.Refinement.value
d_value_38 :: T_Refinement_28 -> AgdaAny
d_value_38 v0
  = case coe v0 of
      C__'44'__42 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Refinement.Base.Refinement.proof
d_proof_40 ::
  T_Refinement_28 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_proof_40 = erased
-- Data.Refinement.Base.Refinement-syntax
d_Refinement'45'syntax_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> ()
d_Refinement'45'syntax_44 = erased
-- Data.Refinement.Base._.map
d_map_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Refinement_28 -> T_Refinement_28
d_map_62 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 v10
  = du_map_62 v8 v10
du_map_62 ::
  (AgdaAny -> AgdaAny) -> T_Refinement_28 -> T_Refinement_28
du_map_62 v0 v1
  = case coe v1 of
      C__'44'__42 v2 -> coe C__'44'__42 (coe v0 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Refinement.Base._.refine
d_refine_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Refinement_28 -> T_Refinement_28
d_refine_86 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_refine_86
du_refine_86 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Refinement_28 -> T_Refinement_28
du_refine_86 v0 v1 = coe du_map_62 (coe (\ v2 -> v2)) v1
