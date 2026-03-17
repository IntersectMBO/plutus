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

module MAlonzo.Code.Data.List.Relation.Unary.Linked where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Maybe.Relation.Binary.Connected
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.List.Relation.Unary.Linked.Linked
d_Linked_28 a0 a1 a2 a3 a4 = ()
data T_Linked_28
  = C_'91''93'_32 | C_'91''45''93'_36 |
    C__'8759'__44 AgdaAny T_Linked_28
-- Data.List.Relation.Unary.Linked._.head
d_head_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> [AgdaAny] -> T_Linked_28 -> AgdaAny
d_head_60 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_head_60 v7
du_head_60 :: T_Linked_28 -> AgdaAny
du_head_60 v0
  = case coe v0 of
      C__'8759'__44 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked._.tail
d_tail_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> [AgdaAny] -> T_Linked_28 -> T_Linked_28
d_tail_70 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_tail_70 v6
du_tail_70 :: T_Linked_28 -> T_Linked_28
du_tail_70 v0
  = case coe v0 of
      C_'91''45''93'_36 -> coe C_'91''93'_32
      C__'8759'__44 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked._.head′
d_head'8242'_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] ->
  T_Linked_28 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.T_Connected_42
d_head'8242'_78 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_head'8242'_78 v6
du_head'8242'_78 ::
  T_Linked_28 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.T_Connected_42
du_head'8242'_78 v0
  = case coe v0 of
      C_'91''45''93'_36
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.C_just'45'nothing_52
      C__'8759'__44 v4 v5
        -> coe
             MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.C_just_50 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked._._∷′_
d__'8759''8242'__86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.T_Connected_42 ->
  T_Linked_28 -> T_Linked_28
d__'8759''8242'__86 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du__'8759''8242'__86 v5 v6 v7
du__'8759''8242'__86 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.T_Connected_42 ->
  T_Linked_28 -> T_Linked_28
du__'8759''8242'__86 v0 v1 v2
  = case coe v0 of
      [] -> coe C_'91''45''93'_36
      (:) v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.C_just_50 v7
               -> coe C__'8759'__44 v7 v2
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked._.map
d_map_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> T_Linked_28 -> T_Linked_28
d_map_108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 = du_map_108 v6 v7 v8
du_map_108 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] -> T_Linked_28 -> T_Linked_28
du_map_108 v0 v1 v2
  = case coe v2 of
      C_'91''93'_32 -> coe v2
      C_'91''45''93'_36 -> coe C_'91''45''93'_36
      C__'8759'__44 v6 v7
        -> case coe v1 of
             (:) v8 v9
               -> case coe v9 of
                    (:) v10 v11
                      -> coe
                           C__'8759'__44 (coe v0 v8 v10 v6)
                           (coe du_map_108 (coe v0) (coe v9) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked._.zipWith
d_zipWith_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Linked_28
d_zipWith_136 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_zipWith_136 v8 v9 v10
du_zipWith_136 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Linked_28
du_zipWith_136 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_'91''93'_32 -> coe seq (coe v4) (coe v3)
             C_'91''45''93'_36 -> coe seq (coe v4) (coe C_'91''45''93'_36)
             C__'8759'__44 v8 v9
               -> case coe v1 of
                    (:) v10 v11
                      -> case coe v11 of
                           (:) v12 v13
                             -> case coe v4 of
                                  C__'8759'__44 v17 v18
                                    -> coe
                                         C__'8759'__44
                                         (coe
                                            v0 v10 v12
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                               (coe v17)))
                                         (coe
                                            du_zipWith_136 (coe v0) (coe v11)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                                               (coe v18)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked._.unzipWith
d_unzipWith_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [AgdaAny] -> T_Linked_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzipWith_152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_unzipWith_152 v8 v9 v10
du_unzipWith_152 ::
  (AgdaAny ->
   AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  [AgdaAny] -> T_Linked_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzipWith_152 v0 v1 v2
  = case coe v2 of
      C_'91''93'_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v2)
      C_'91''45''93'_36
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_'91''45''93'_36)
             (coe C_'91''45''93'_36)
      C__'8759'__44 v6 v7
        -> case coe v1 of
             (:) v8 v9
               -> case coe v9 of
                    (:) v10 v11
                      -> coe
                           MAlonzo.Code.Data.Product.Base.du_zip_198 (coe C__'8759'__44)
                           (coe (\ v12 v13 -> coe C__'8759'__44)) (coe v0 v8 v10 v6)
                           (coe du_unzipWith_152 (coe v0) (coe v9) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked._.zip
d_zip_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Linked_28
d_zip_176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_zip_176 v6
du_zip_176 ::
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Linked_28
du_zip_176 v0
  = coe du_zipWith_136 (coe (\ v1 v2 v3 -> v3)) (coe v0)
-- Data.List.Relation.Unary.Linked._.unzip
d_unzip_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] -> T_Linked_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzip_178 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_unzip_178 v6
du_unzip_178 ::
  [AgdaAny] -> T_Linked_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzip_178 v0
  = coe du_unzipWith_152 (coe (\ v1 v2 v3 -> v3)) (coe v0)
-- Data.List.Relation.Unary.Linked.lookup
d_lookup_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Linked_28 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.T_Connected_42 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_lookup_186 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_lookup_186 v4 v5 v6 v7 v8 v9
du_lookup_186 ::
  AgdaAny ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  T_Linked_28 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.T_Connected_42 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_lookup_186 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      C_'91''45''93'_36
        -> case coe v4 of
             MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.C_just_50 v9
               -> coe seq (coe v5) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8759'__44 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v12 of
                    (:) v13 v14
                      -> case coe v4 of
                           MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.C_just_50 v17
                             -> case coe v5 of
                                  MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v17
                                  MAlonzo.Code.Data.Fin.Base.C_suc_16 v19
                                    -> coe
                                         du_lookup_186 (coe v0) (coe v12) (coe v2) (coe v10)
                                         (coe
                                            MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.C_just_50
                                            (coe v2 v0 v11 v13 v17 v9))
                                         (coe v19)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked._.linked?
d_linked'63'_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_linked'63'_218 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_linked'63'_218 v4 v5
du_linked'63'_218 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_linked'63'_218 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe C_'91''93'_32))
      (:) v2 v3
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe C_'91''45''93'_36))
             (:) v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    (coe
                       MAlonzo.Code.Data.Product.Base.du_uncurry_244 (coe C__'8759'__44))
                    (coe
                       MAlonzo.Code.Data.Product.Base.du_'60'_'44'_'62'_112
                       (coe du_head_60) (coe du_tail_70))
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                       (coe v0 v2 v4) (coe du_linked'63'_218 (coe v0) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked._.irrelevant
d_irrelevant_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  T_Linked_28 ->
  T_Linked_28 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irrelevant_234 = erased
-- Data.List.Relation.Unary.Linked._.satisfiable
d_satisfiable_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfiable_250 ~v0 ~v1 ~v2 ~v3 = du_satisfiable_250
du_satisfiable_250 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfiable_250
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe C_'91''93'_32)
