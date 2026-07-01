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

module MAlonzo.Code.Data.Vec where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Data.Vec.Bounded.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.Vec._.filter
d_filter_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Bounded.Base.T_Vec'8804'_126
d_filter_24 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 = du_filter_24 v4 v6
du_filter_24 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Bounded.Base.T_Vec'8804'_126
du_filter_24 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe MAlonzo.Code.Data.Vec.Bounded.Base.du_'91''93'_256
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe v0 v3))
             (coe MAlonzo.Code.Data.Vec.Bounded.Base.du__'8759'__258 (coe v3))
             (\ v5 -> v5) (coe du_filter_24 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec._.takeWhile
d_takeWhile_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Bounded.Base.T_Vec'8804'_126
d_takeWhile_34 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 = du_takeWhile_34 v4 v6
du_takeWhile_34 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Bounded.Base.T_Vec'8804'_126
du_takeWhile_34 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe MAlonzo.Code.Data.Vec.Bounded.Base.du_'91''93'_256
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28 (coe v0 v3))
             (coe
                MAlonzo.Code.Data.Vec.Bounded.Base.du__'8759'__258 (coe v3)
                (coe du_takeWhile_34 (coe v0) (coe v4)))
             (coe MAlonzo.Code.Data.Vec.Bounded.Base.du_'91''93'_256)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec._.dropWhile
d_dropWhile_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Bounded.Base.T_Vec'8804'_126
d_dropWhile_42 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_dropWhile_42 v4 v5 v6
du_dropWhile_42 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Bounded.Base.T_Vec'8804'_126
du_dropWhile_42 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe MAlonzo.Code.Data.Vec.Bounded.Base.du_'91''93'_256
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4 v5
        -> let v6 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                (coe
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28 (coe v0 v4))
                (coe du_dropWhile_42 (coe v0) (coe v6) (coe v5))
                (coe
                   MAlonzo.Code.Data.Vec.Bounded.Base.du_fromVec_162 (coe v1)
                   (coe MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4 v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
