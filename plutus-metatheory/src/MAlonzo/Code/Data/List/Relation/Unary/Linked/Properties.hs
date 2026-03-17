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

module MAlonzo.Code.Data.List.Relation.Unary.Linked.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.List.Relation.Unary.Linked
import qualified MAlonzo.Code.Data.Maybe.Relation.Binary.Connected
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.List.Relation.Unary.Linked.Properties._.AllPairs⇒Linked
d_AllPairs'8658'Linked_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_AllPairs'8658'Linked_36 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_AllPairs'8658'Linked_36 v4 v5
du_AllPairs'8658'Linked_36 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
du_AllPairs'8658'Linked_36 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22
        -> coe MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''93'_32
      MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28 v4 v5
        -> case coe v0 of
             (:) v6 v7
               -> case coe v5 of
                    MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
                    MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28 v10 v11
                      -> case coe v4 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v14 v15
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v14
                                  (coe
                                     du_AllPairs'8658'Linked_36 (coe v7)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                                        v10 v11))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked.Properties._.Linked⇒All
d_Linked'8658'All_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_Linked'8658'All_64 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_Linked'8658'All_64 v4 v5 v6 v7 v8 v9
du_Linked'8658'All_64 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_Linked'8658'All_64 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v9 v10
        -> case coe v3 of
             (:) v11 v12
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4
                    (coe
                       du_Linked'8658'All_64 (coe v0) (coe v1) (coe v11) (coe v12)
                       (coe v0 v1 v2 v11 v4 v9) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked.Properties._.Linked⇒AllPairs
d_Linked'8658'AllPairs_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_Linked'8658'AllPairs_76 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_Linked'8658'AllPairs_76 v4 v5 v6
du_Linked'8658'AllPairs_76 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_Linked'8658'AllPairs_76 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''93'_32
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22)
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v6 v7
        -> case coe v1 of
             (:) v8 v9
               -> case coe v9 of
                    (:) v10 v11
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                           (coe
                              du_Linked'8658'All_64 (coe v0) (coe v8) (coe v10) (coe v11)
                              (coe v6) (coe v7))
                           (coe du_Linked'8658'AllPairs_76 (coe v0) (coe v9) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked.Properties._.map⁺
d_map'8314'_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_map'8314'_98 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_map'8314'_98 v7 v8
du_map'8314'_98 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
du_map'8314'_98 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''93'_32
        -> coe v1
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v5
                    (coe du_map'8314'_98 (coe v8) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked.Properties._.map⁻
d_map'8315'_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_map'8315'_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_map'8315'_106 v7 v8
du_map'8315'_106 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
du_map'8315'_106 v0 v1
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''93'_32)
      (:) v2 v3
        -> case coe v3 of
             []
               -> coe
                    seq (coe v1)
                    (coe
                       MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36)
             (:) v4 v5
               -> case coe v1 of
                    MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v9 v10
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v9
                           (coe du_map'8315'_106 (coe v3) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked.Properties._.++⁺
d_'43''43''8314'_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.T_Connected_42 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_'43''43''8314'_134 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 v7 v8
  = du_'43''43''8314'_134 v4 v6 v7 v8
du_'43''43''8314'_134 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.T_Connected_42 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
du_'43''43''8314'_134 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''93'_32
        -> coe v3
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
        -> case coe v3 of
             MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''93'_32
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
             MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
               -> case coe v2 of
                    MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.C_just_50 v8
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v8
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v8 v9
               -> case coe v2 of
                    MAlonzo.Code.Data.Maybe.Relation.Binary.Connected.C_just_50 v12
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v12
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v8 v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v7
                    (coe du_'43''43''8314'_134 (coe v10) (coe v8) (coe v2) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked.Properties._.applyUpTo⁺₁
d_applyUpTo'8314''8321'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (Integer -> AgdaAny) ->
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_applyUpTo'8314''8321'_170 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_applyUpTo'8314''8321'_170 v5 v6
du_applyUpTo'8314''8321'_170 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
du_applyUpTo'8314''8321'_170 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''93'_32
      1 -> coe
             MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
      _ -> coe
             MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44
             (coe
                v1 (0 :: Integer)
                (coe
                   MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                   (coe
                      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                      (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))))
             (coe
                du_applyUpTo'8314''8321'_170
                (coe subInt (coe v0) (coe (1 :: Integer)))
                (coe
                   (\ v2 v3 ->
                      coe
                        v1 (addInt (coe (1 :: Integer)) (coe v2))
                        (coe MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v3))))
-- Data.List.Relation.Unary.Linked.Properties._.applyUpTo⁺₂
d_applyUpTo'8314''8322'_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (Integer -> AgdaAny) ->
  Integer ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_applyUpTo'8314''8322'_192 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_applyUpTo'8314''8322'_192 v5 v6
du_applyUpTo'8314''8322'_192 ::
  Integer ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
du_applyUpTo'8314''8322'_192 v0 v1
  = coe
      du_applyUpTo'8314''8321'_170 (coe v0) (coe (\ v2 v3 -> coe v1 v2))
-- Data.List.Relation.Unary.Linked.Properties._.applyDownFrom⁺₁
d_applyDownFrom'8314''8321'_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (Integer -> AgdaAny) ->
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_applyDownFrom'8314''8321'_218 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_applyDownFrom'8314''8321'_218 v5 v6
du_applyDownFrom'8314''8321'_218 ::
  Integer ->
  (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
du_applyDownFrom'8314''8321'_218 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''93'_32
      1 -> coe
             MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
      _ -> let v2 = subInt (coe v0) (coe (2 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44
                (coe
                   v1 v2
                   (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2814 (coe v0)))
                (coe
                   du_applyDownFrom'8314''8321'_218
                   (coe subInt (coe v0) (coe (1 :: Integer)))
                   (coe (\ v3 v4 -> coe v1 v3 v4))))
-- Data.List.Relation.Unary.Linked.Properties._.applyDownFrom⁺₂
d_applyDownFrom'8314''8322'_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (Integer -> AgdaAny) ->
  Integer ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_applyDownFrom'8314''8322'_240 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_applyDownFrom'8314''8322'_240 v5 v6
du_applyDownFrom'8314''8322'_240 ::
  Integer ->
  (Integer -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
du_applyDownFrom'8314''8322'_240 v0 v1
  = coe
      du_applyDownFrom'8314''8321'_218 (coe v0)
      (coe (\ v2 v3 -> coe v1 v2))
-- Data.List.Relation.Unary.Linked.Properties._.∷-filter⁺
d_'8759''45'filter'8314'_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_'8759''45'filter'8314'_272 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9
                             v10
  = du_'8759''45'filter'8314'_272 v5 v7 v8 v9 v10
du_'8759''45'filter'8314'_272 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
du_'8759''45'filter'8314'_272 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
        -> coe
             MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v8 v9
        -> case coe v3 of
             (:) v10 v11
               -> case coe v9 of
                    MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
                      -> let v13
                               = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                   (coe v0 v10) in
                         coe
                           (if coe v13
                              then coe
                                     MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v8
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36)
                              else coe
                                     MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36)
                    MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v15 v16
                      -> case coe v11 of
                           (:) v17 v18
                             -> let v19
                                      = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                          (coe v0 v10) in
                                coe
                                  (let v20
                                         = coe
                                             du_'8759''45'filter'8314'_272 (coe v0) (coe v1)
                                             (coe v2) (coe v11) in
                                   coe
                                     (let v21
                                            = coe
                                                du_'8759''45'filter'8314'_272 (coe v0) (coe v1)
                                                (coe v10) (coe v11)
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44
                                                   v15 v16) in
                                      coe
                                        (if coe v19
                                           then coe
                                                  MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44
                                                  v8 v21
                                           else coe
                                                  v20
                                                  (coe
                                                     MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44
                                                     (coe v1 v2 v10 v17 v8 v15) v16))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Unary.Linked.Properties._.filter⁺
d_filter'8314'_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
d_filter'8314'_336 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9
  = du_filter'8314'_336 v5 v7 v8 v9
du_filter'8314'_336 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28 ->
  MAlonzo.Code.Data.List.Relation.Unary.Linked.T_Linked_28
du_filter'8314'_336 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''93'_32
        -> coe v3
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
        -> case coe v2 of
             (:) v5 v6
               -> coe
                    seq (coe v6)
                    (let v7
                           = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                               (coe v0 v5) in
                     coe
                       (if coe v7
                          then coe
                                 MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''45''93'_36
                          else coe
                                 MAlonzo.Code.Data.List.Relation.Unary.Linked.C_'91''93'_32))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v7 v8
        -> case coe v2 of
             (:) v9 v10
               -> let v11
                        = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                            (coe v0 v9) in
                  coe
                    (if coe v11
                       then coe
                              du_'8759''45'filter'8314'_272 (coe v0) (coe v1) (coe v9) (coe v10)
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Unary.Linked.C__'8759'__44 v7 v8)
                       else coe du_filter'8314'_336 (coe v0) (coe v1) (coe v10) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
