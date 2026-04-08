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

module MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Product.Base

-- Data.List.Relation.Binary.Pointwise.Base.Pointwise
d_Pointwise_48 a0 a1 a2 a3 a4 a5 a6 a7 = ()
data T_Pointwise_48
  = C_'91''93'_56 | C__'8759'__62 AgdaAny T_Pointwise_48
-- Data.List.Relation.Binary.Pointwise.Base.head
d_head_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] -> AgdaAny -> [AgdaAny] -> T_Pointwise_48 -> AgdaAny
d_head_64 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_head_64 v10
du_head_64 :: T_Pointwise_48 -> AgdaAny
du_head_64 v0
  = case coe v0 of
      C__'8759'__62 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.Base.tail
d_tail_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny -> [AgdaAny] -> T_Pointwise_48 -> T_Pointwise_48
d_tail_70 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_tail_70 v10
du_tail_70 :: T_Pointwise_48 -> T_Pointwise_48
du_tail_70 v0
  = case coe v0 of
      C__'8759'__62 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.Base.uncons
d_uncons_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  [AgdaAny] ->
  T_Pointwise_48 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_uncons_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 = du_uncons_76
du_uncons_76 ::
  T_Pointwise_48 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_uncons_76
  = coe
      MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112
      (coe du_head_64) (coe du_tail_70)
-- Data.List.Relation.Binary.Pointwise.Base.rec
d_rec_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ([AgdaAny] -> [AgdaAny] -> T_Pointwise_48 -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   [AgdaAny] ->
   [AgdaAny] -> T_Pointwise_48 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> [AgdaAny] -> T_Pointwise_48 -> AgdaAny
d_rec_102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 v12
  = du_rec_102 v8 v9 v10 v11 v12
du_rec_102 ::
  (AgdaAny ->
   AgdaAny ->
   [AgdaAny] ->
   [AgdaAny] -> T_Pointwise_48 -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> [AgdaAny] -> T_Pointwise_48 -> AgdaAny
du_rec_102 v0 v1 v2 v3 v4
  = case coe v4 of
      C_'91''93'_56 -> coe v1
      C__'8759'__62 v9 v10
        -> case coe v2 of
             (:) v11 v12
               -> case coe v3 of
                    (:) v13 v14
                      -> coe
                           v0 v11 v13 v12 v14 v10 v9
                           (coe du_rec_102 (coe v0) (coe v1) (coe v12) (coe v14) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.Base.map
d_map_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> T_Pointwise_48 -> T_Pointwise_48
d_map_120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
  = du_map_120 v8 v9 v10 v11
du_map_120 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> [AgdaAny] -> T_Pointwise_48 -> T_Pointwise_48
du_map_120 v0 v1 v2 v3
  = case coe v3 of
      C_'91''93'_56 -> coe v3
      C__'8759'__62 v8 v9
        -> case coe v1 of
             (:) v10 v11
               -> case coe v2 of
                    (:) v12 v13
                      -> coe
                           C__'8759'__62 (coe v0 v10 v12 v8)
                           (coe du_map_120 (coe v0) (coe v11) (coe v13) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.Base.unzip
d_unzip_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  T_Pointwise_48 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzip_130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12
  = du_unzip_130 v10 v11 v12
du_unzip_130 ::
  [AgdaAny] ->
  [AgdaAny] ->
  T_Pointwise_48 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzip_130 v0 v1 v2
  = case coe v2 of
      C_'91''93'_56
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v2))
      C__'8759'__62 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    (:) v11 v12
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v14 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> coe
                                         MAlonzo.Code.Data.Product.Base.du_map_128
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v13))
                                         (coe
                                            (\ v17 ->
                                               coe
                                                 MAlonzo.Code.Data.Product.Base.du_map_128
                                                 (coe C__'8759'__62 v15)
                                                 (coe (\ v18 -> coe C__'8759'__62 v16))))
                                         (coe du_unzip_130 (coe v10) (coe v12) (coe v8))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
