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

module MAlonzo.Code.Data.Maybe.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.These.Base
import qualified MAlonzo.Code.Level

-- Data.Maybe.Base.boolToMaybe
d_boolToMaybe_18 ::
  Bool -> Maybe MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_boolToMaybe_18 v0
  = if coe v0
      then coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      else coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Data.Maybe.Base.is-just
d_is'45'just_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Maybe AgdaAny -> Bool
d_is'45'just_20 ~v0 ~v1 v2 = du_is'45'just_20 v2
du_is'45'just_20 :: Maybe AgdaAny -> Bool
du_is'45'just_20 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Base.is-nothing
d_is'45'nothing_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Maybe AgdaAny -> Bool
d_is'45'nothing_22 ~v0 ~v1 v2 = du_is'45'nothing_22 v2
du_is'45'nothing_22 :: Maybe AgdaAny -> Bool
du_is'45'nothing_22 v0
  = coe
      MAlonzo.Code.Data.Bool.Base.d_not_22
      (coe du_is'45'just_20 (coe v0))
-- Data.Maybe.Base.maybe
d_maybe_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Maybe AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> Maybe AgdaAny -> AgdaAny
d_maybe_32 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_maybe_32 v4 v5 v6
du_maybe_32 ::
  (AgdaAny -> AgdaAny) -> AgdaAny -> Maybe AgdaAny -> AgdaAny
du_maybe_32 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3 -> coe v0 v3
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Base.maybe′
d_maybe'8242'_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> Maybe AgdaAny -> AgdaAny
d_maybe'8242'_44 ~v0 ~v1 ~v2 ~v3 = du_maybe'8242'_44
du_maybe'8242'_44 ::
  (AgdaAny -> AgdaAny) -> AgdaAny -> Maybe AgdaAny -> AgdaAny
du_maybe'8242'_44 = coe du_maybe_32
-- Data.Maybe.Base.fromMaybe
d_fromMaybe_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> Maybe AgdaAny -> AgdaAny
d_fromMaybe_46 ~v0 ~v1 = du_fromMaybe_46
du_fromMaybe_46 :: AgdaAny -> Maybe AgdaAny -> AgdaAny
du_fromMaybe_46 = coe du_maybe'8242'_44 (\ v0 -> v0)
-- Data.Maybe.Base._.From-just
d_From'45'just_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> Maybe AgdaAny -> ()
d_From'45'just_56 = erased
-- Data.Maybe.Base._.from-just
d_from'45'just_60 :: Maybe AgdaAny -> AgdaAny
d_from'45'just_60 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1 -> coe v1
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Level.C_lift_20
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Base.map
d_map_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d_map_64 ~v0 ~v1 ~v2 ~v3 v4 = du_map_64 v4
du_map_64 :: (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
du_map_64 v0
  = coe
      du_maybe_32
      (coe
         (\ v1 ->
            coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v1)))
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Data.Maybe.Base.ap
d_ap_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Maybe (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d_ap_68 ~v0 ~v1 ~v2 ~v3 v4 = du_ap_68 v4
du_ap_68 ::
  Maybe (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
du_ap_68 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe du_map_64 (coe v1)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (\ v1 -> v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Base._>>=_
d__'62''62''61'__72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Maybe AgdaAny -> (AgdaAny -> Maybe AgdaAny) -> Maybe AgdaAny
d__'62''62''61'__72 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du__'62''62''61'__72 v4 v5
du__'62''62''61'__72 ::
  Maybe AgdaAny -> (AgdaAny -> Maybe AgdaAny) -> Maybe AgdaAny
du__'62''62''61'__72 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v1 v2
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Base._<∣>_
d__'60''8739''62'__80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d__'60''8739''62'__80 ~v0 ~v1 v2 v3 = du__'60''8739''62'__80 v2 v3
du__'60''8739''62'__80 ::
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
du__'60''8739''62'__80 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v0
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Base.when
d_when_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Bool -> AgdaAny -> Maybe AgdaAny
d_when_88 ~v0 ~v1 v2 v3 = du_when_88 v2 v3
du_when_88 :: Bool -> AgdaAny -> Maybe AgdaAny
du_when_88 v0 v1
  = coe du_map_64 (\ v2 -> v1) (d_boolToMaybe_18 (coe v0))
-- Data.Maybe.Base.alignWith
d_alignWith_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d_alignWith_94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_alignWith_94 v6 v7 v8
du_alignWith_94 ::
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
du_alignWith_94 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe
                       v0 (coe MAlonzo.Code.Data.These.Base.C_these_52 (coe v3) (coe v4)))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe v0 (coe MAlonzo.Code.Data.These.Base.C_this_48 (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                    (coe v0 (coe MAlonzo.Code.Data.These.Base.C_that_50 (coe v3)))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Base.zipWith
d_zipWith_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d_zipWith_112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_zipWith_112 v6 v7 v8
du_zipWith_112 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
du_zipWith_112 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0 v4 v5)
                _ -> coe v3
         _ -> coe v3)
-- Data.Maybe.Base.align
d_align_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Data.These.Base.T_These_38
d_align_120 ~v0 ~v1 ~v2 ~v3 = du_align_120
du_align_120 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Data.These.Base.T_These_38
du_align_120 = coe du_alignWith_94 (coe (\ v0 -> v0))
-- Data.Maybe.Base.zip
d_zip_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zip_122 ~v0 ~v1 ~v2 ~v3 = du_zip_122
du_zip_122 ::
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zip_122
  = coe
      du_zipWith_112 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32)
-- Data.Maybe.Base.thisM
d_thisM_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny -> Maybe AgdaAny -> MAlonzo.Code.Data.These.Base.T_These_38
d_thisM_124 ~v0 ~v1 ~v2 ~v3 v4 = du_thisM_124 v4
du_thisM_124 ::
  AgdaAny -> Maybe AgdaAny -> MAlonzo.Code.Data.These.Base.T_These_38
du_thisM_124 v0
  = coe
      du_maybe'8242'_44
      (coe MAlonzo.Code.Data.These.Base.C_these_52 (coe v0))
      (coe MAlonzo.Code.Data.These.Base.C_this_48 (coe v0))
-- Data.Maybe.Base.thatM
d_thatM_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Maybe AgdaAny -> AgdaAny -> MAlonzo.Code.Data.These.Base.T_These_38
d_thatM_128 ~v0 ~v1 ~v2 ~v3 = du_thatM_128
du_thatM_128 ::
  Maybe AgdaAny -> AgdaAny -> MAlonzo.Code.Data.These.Base.T_These_38
du_thatM_128
  = coe
      du_maybe'8242'_44 (coe MAlonzo.Code.Data.These.Base.C_these_52)
      (coe MAlonzo.Code.Data.These.Base.C_that_50)
