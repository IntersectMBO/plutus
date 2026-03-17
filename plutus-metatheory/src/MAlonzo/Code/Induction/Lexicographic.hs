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

module MAlonzo.Code.Induction.Lexicographic where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive

-- Induction.Lexicographic.Σ-Rec
d_Σ'45'Rec_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> ()) -> AgdaAny -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_Σ'45'Rec_20 = erased
-- Induction.Lexicographic._⊗_
d__'8855'__52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d__'8855'__52 = erased
-- Induction.Lexicographic.Σ-rec-builder
d_Σ'45'rec'45'builder_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_Σ'45'rec'45'builder_82 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
                         ~v11 v12 v13
  = du_Σ'45'rec'45'builder_82 v9 v10 v12 v13
du_Σ'45'rec'45'builder_82 ::
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_Σ'45'rec'45'builder_82 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_p'8321'_114 (coe v1) erased (coe v2) (coe v4) (coe v5)
                (coe du_p'8322'x_146 (coe v0) (coe v1) (coe v2) (coe v4)))
             (coe du_p'8322'x_146 (coe v0) (coe v1) (coe v2) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Induction.Lexicographic._.p₁
d_p'8321'_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_p'8321'_114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12
              ~v13 ~v14 v15 v16 v17
  = du_p'8321'_114 v10 v11 v12 v15 v16 v17
du_p'8321'_114 ::
  (AgdaAny ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_p'8321'_114 v0 v1 v2 v3 v4 v5
  = coe
      v0 v3
      (\ v6 ->
         coe
           v1
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v6)))
      (\ v6 v7 ->
         coe
           v2
           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v6))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7) (coe v5)))
      v4
-- Induction.Lexicographic._.p₂
d_p'8322'_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_p'8322'_134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 v12
              ~v13 ~v14
  = du_p'8322'_134 v9 v10 v12
du_p'8322'_134 ::
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  AgdaAny -> AgdaAny
du_p'8322'_134 v0 v1 v2
  = coe
      v0 (\ v3 -> ())
      (\ v3 v4 v5 ->
         coe
           v2
           (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v5))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 du_p'8321'_114 (coe v1) erased (coe v2) (coe v3) (coe v5) (coe v4))
              (coe v4)))
-- Induction.Lexicographic._.p₂x
d_p'8322'x_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  (AgdaAny -> (AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_p'8322'x_146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 ~v11 v12
               v13 ~v14
  = du_p'8322'x_146 v9 v10 v12 v13
du_p'8322'x_146 ::
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  AgdaAny -> AgdaAny
du_p'8322'x_146 v0 v1 v2 v3 = coe du_p'8322'_134 v0 v1 v2 v3
-- Induction.Lexicographic.[_⊗_]
d_'91'_'8855'_'93'_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) -> AgdaAny -> ()) ->
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'91'_'8855'_'93'_166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_'91'_'8855'_'93'_166 v9 v10
du_'91'_'8855'_'93'_166 ::
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  ((AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'91'_'8855'_'93'_166 v0 v1 v2 v3 v4
  = coe du_Σ'45'rec'45'builder_82 (coe v0) (coe (\ v5 -> v1)) v3 v4
