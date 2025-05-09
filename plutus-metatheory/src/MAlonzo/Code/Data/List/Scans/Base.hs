{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Data.List.Scans.Base where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.List qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.List.NonEmpty.Base qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.List.Scans.Base._.scanr⁺
d_scanr'8314'_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22
d_scanr'8314'_28 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_scanr'8314'_28 v4 v5 v6
du_scanr'8314'_28 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22
du_scanr'8314'_28 v0 v1 v2
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Data.List.NonEmpty.Base.C__'8759'__34 (coe v1)
             (coe v2)
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.List.NonEmpty.Base.C__'8759'__34
             (coe
                v0 v3
                (MAlonzo.Code.Data.List.NonEmpty.Base.d_head_30
                   (coe du_scanr'8314'_28 (coe v0) (coe v1) (coe v4))))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Data.List.NonEmpty.Base.d_head_30
                   (coe du_scanr'8314'_28 (coe v0) (coe v1) (coe v4)))
                (coe
                   MAlonzo.Code.Data.List.NonEmpty.Base.d_tail_32
                   (coe du_scanr'8314'_28 (coe v0) (coe v1) (coe v4))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Scans.Base._.scanr
d_scanr_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> [AgdaAny]
d_scanr_44 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_scanr_44 v4 v5 v6
du_scanr_44 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> [AgdaAny]
du_scanr_44 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.NonEmpty.Base.du_toList_60
      (coe du_scanr'8314'_28 (coe v0) (coe v1) (coe v2))
-- Data.List.Scans.Base._.scanl⁺
d_scanl'8314'_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22
d_scanl'8314'_58 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_scanl'8314'_58 v4 v5 v6
du_scanl'8314'_58 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Data.List.NonEmpty.Base.T_List'8314'_22
du_scanl'8314'_58 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.NonEmpty.Base.C__'8759'__34 (coe v1)
      (coe du_go_68 (coe v0) (coe v1) (coe v2))
-- Data.List.Scans.Base._._.go
d_go_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> AgdaAny -> [AgdaAny] -> [AgdaAny]
d_go_68 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8 = du_go_68 v4 v7 v8
du_go_68 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> [AgdaAny]
du_go_68 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0 v1 v3)
             (coe du_go_68 (coe v0) (coe v0 v1 v3) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Scans.Base._.scanl
d_scanl_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> [AgdaAny]
d_scanl_78 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_scanl_78 v4 v5 v6
du_scanl_78 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> [AgdaAny] -> [AgdaAny]
du_scanl_78 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.NonEmpty.Base.du_toList_60
      (coe du_scanl'8314'_58 (coe v0) (coe v1) (coe v2))
