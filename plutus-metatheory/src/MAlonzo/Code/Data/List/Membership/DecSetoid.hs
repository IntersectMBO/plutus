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

module MAlonzo.Code.Data.List.Membership.DecSetoid where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.List.Membership.Setoid qualified
import MAlonzo.Code.Data.List.Relation.Unary.Any qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.List.Membership.DecSetoid._._∈_
d__'8712'__44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  AgdaAny -> [AgdaAny] -> ()
d__'8712'__44 = erased
-- Data.List.Membership.DecSetoid._._∉_
d__'8713'__46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  AgdaAny -> [AgdaAny] -> ()
d__'8713'__46 = erased
-- Data.List.Membership.DecSetoid._._∷=_
d__'8759''61'__48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [AgdaAny] ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> [AgdaAny]
d__'8759''61'__48 ~v0 ~v1 ~v2 = du__'8759''61'__48
du__'8759''61'__48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [AgdaAny] ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> [AgdaAny]
du__'8759''61'__48
  = coe MAlonzo.Code.Data.List.Membership.Setoid.du__'8759''61'__50
-- Data.List.Membership.DecSetoid._._─_
d__'9472'__50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> [AgdaAny]
d__'9472'__50 ~v0 ~v1 ~v2 = du__'9472'__50
du__'9472'__50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> [AgdaAny]
du__'9472'__50
  = coe MAlonzo.Code.Data.List.Membership.Setoid.du__'9472'__52
-- Data.List.Membership.DecSetoid._.find
d_find_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_find_52 ~v0 ~v1 v2 = du_find_52 v2
du_find_52 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_find_52 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Membership.Setoid.du_find_84
      (coe MAlonzo.Code.Relation.Binary.Bundles.du_setoid_108 (coe v0))
      v3 v4
-- Data.List.Membership.DecSetoid._.lose
d_lose_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_lose_54 ~v0 ~v1 ~v2 = du_lose_54
du_lose_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  AgdaAny -> MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_lose_54 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.List.Membership.Setoid.du_lose_100 v2 v3 v4 v5 v6
-- Data.List.Membership.DecSetoid._.mapWith∈
d_mapWith'8712'_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny) ->
  [AgdaAny]
d_mapWith'8712'_56 ~v0 ~v1 v2 = du_mapWith'8712'_56 v2
du_mapWith'8712'_56 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  (AgdaAny ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 -> AgdaAny) ->
  [AgdaAny]
du_mapWith'8712'_56 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Membership.Setoid.du_mapWith'8712'_62
      (coe MAlonzo.Code.Relation.Binary.Bundles.du_setoid_108 (coe v0))
      v3 v4
-- Data.List.Membership.DecSetoid._∈?_
d__'8712''63'__58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8712''63'__58 ~v0 ~v1 v2 v3 v4 = du__'8712''63'__58 v2 v3 v4
du__'8712''63'__58 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8712''63'__58 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.Any.du_any'63'_138
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d__'8799'__52
         (MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_100
            (coe v0))
         v1)
      (coe v2)
-- Data.List.Membership.DecSetoid._∉?_
d__'8713''63'__66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8713''63'__66 ~v0 ~v1 v2 v3 v4 = du__'8713''63'__66 v2 v3 v4
du__'8713''63'__66 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  AgdaAny ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8713''63'__66 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_70
      (coe du__'8712''63'__58 (coe v0) (coe v1) (coe v2))
