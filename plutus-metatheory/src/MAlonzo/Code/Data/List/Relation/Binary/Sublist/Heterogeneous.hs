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

module MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any

-- Data.List.Relation.Binary.Sublist.Heterogeneous._.map
d_map_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_map_32 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
  = du_map_32 v8 v9 v10 v11
du_map_32 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_map_32 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C_'91''93'_28
        -> coe v3
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v7
        -> case coe v2 of
             (:) v8 v9
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36
                    (coe du_map_32 (coe v0) (coe v1) (coe v9) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46 v8 v9
        -> case coe v1 of
             (:) v10 v11
               -> case coe v2 of
                    (:) v12 v13
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
                           (coe v0 v10 v12 v8)
                           (coe du_map_32 (coe v0) (coe v11) (coe v13) (coe v9))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Heterogeneous.minimum
d_minimum_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_minimum_48 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_minimum_48 v6
du_minimum_48 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_minimum_48 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C_'91''93'_28
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36
             (coe du_minimum_48 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Heterogeneous.toAny
d_toAny_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_toAny_60 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_toAny_60 v8 v9
du_toAny_60 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_toAny_60 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v5
        -> case coe v0 of
             (:) v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                    (coe du_toAny_60 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46 v6 v7
        -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Heterogeneous.fromAny
d_fromAny_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
d_fromAny_74 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_fromAny_74 v7 v8
du_fromAny_74 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26
du_fromAny_74 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v4
        -> case coe v0 of
             (:) v5 v6
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46
                    v4 (coe du_minimum_48 (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v4
        -> case coe v0 of
             (:) v5 v6
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36
                    (coe du_fromAny_74 (coe v6) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Heterogeneous._.lookup
d_lookup_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_lookup_98 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11 v12 v13
            v14
  = du_lookup_98 v10 v11 v12 v13 v14
du_lookup_98 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.T_Sublist_26 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_lookup_98 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759''691'__36 v8
        -> case coe v2 of
             (:) v9 v10
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                    (coe du_lookup_98 (coe v0) (coe v1) (coe v10) (coe v8) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Sublist.Heterogeneous.Core.C__'8759'__46 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v2 of
                    (:) v13 v14
                      -> case coe v4 of
                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v17
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                  (coe v0 v11 v13 v9 v17)
                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v17
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                  (coe
                                     du_lookup_98 (coe v0) (coe v12) (coe v14) (coe v10) (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Sublist.Heterogeneous._⊆_
d__'8838'__118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () -> (AgdaAny -> AgdaAny -> ()) -> [AgdaAny] -> [AgdaAny] -> ()
d__'8838'__118 = erased
-- Data.List.Relation.Binary.Sublist.Heterogeneous.Disjoint
d_Disjoint_130 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_Disjoint_130
  = C_'91''93'_132 | C__'8759''8345'__146 T_Disjoint_130 |
    C__'8759''8343'__164 T_Disjoint_130 |
    C__'8759''7523'__182 T_Disjoint_130
-- Data.List.Relation.Binary.Sublist.Heterogeneous.DisjointUnion
d_DisjointUnion_198 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = ()
data T_DisjointUnion_198
  = C_'91''93'_200 | C__'8759''8345'__218 T_DisjointUnion_198 |
    C__'8759''8343'__240 T_DisjointUnion_198 |
    C__'8759''7523'__262 T_DisjointUnion_198
