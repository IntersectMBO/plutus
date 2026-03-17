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

module MAlonzo.Code.Class.Semigroup.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Setoid.Core
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Class.Semigroup.Core.Semigroup
d_Semigroup_10 a0 a1 = ()
newtype T_Semigroup_10
  = C_Semigroup'46'constructor_25 (AgdaAny -> AgdaAny -> AgdaAny)
-- Class.Semigroup.Core.Semigroup._◇_
d__'9671'__16 :: T_Semigroup_10 -> AgdaAny -> AgdaAny -> AgdaAny
d__'9671'__16 v0
  = case coe v0 of
      C_Semigroup'46'constructor_25 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Semigroup.Core.Semigroup._<>_
d__'60''62'__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Semigroup_10 -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''62'__18 ~v0 ~v1 v2 = du__'60''62'__18 v2
du__'60''62'__18 :: T_Semigroup_10 -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''62'__18 v0 = coe d__'9671'__16 (coe v0)
-- Class.Semigroup.Core._._<>_
d__'60''62'__22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Semigroup_10 -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''62'__22 ~v0 ~v1 v2 = du__'60''62'__22 v2
du__'60''62'__22 :: T_Semigroup_10 -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''62'__22 v0 = coe du__'60''62'__18 (coe v0)
-- Class.Semigroup.Core._._◇_
d__'9671'__24 :: T_Semigroup_10 -> AgdaAny -> AgdaAny -> AgdaAny
d__'9671'__24 v0 = coe d__'9671'__16 (coe v0)
-- Class.Semigroup.Core._.SemigroupLaws
d_SemigroupLaws_40 a0 a1 a2 a3 a4 = ()
data T_SemigroupLaws_40
  = C_SemigroupLaws'46'constructor_2433 (AgdaAny ->
                                         AgdaAny -> AgdaAny)
                                        (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny)
-- Class.Semigroup.Core._._.Associative
d_Associative_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_Semigroup_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_ISetoid_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_SetoidLaws_302 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Associative_70 = erased
-- Class.Semigroup.Core._._.Commutative
d_Commutative_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_Semigroup_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_ISetoid_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_SetoidLaws_302 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Commutative_74 = erased
-- Class.Semigroup.Core._.SemigroupLaws.◇-comm
d_'9671''45'comm_310 ::
  T_SemigroupLaws_40 -> AgdaAny -> AgdaAny -> AgdaAny
d_'9671''45'comm_310 v0
  = case coe v0 of
      C_SemigroupLaws'46'constructor_2433 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Semigroup.Core._.SemigroupLaws.◇-assocʳ
d_'9671''45'assoc'691'_312 ::
  T_SemigroupLaws_40 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'9671''45'assoc'691'_312 v0
  = case coe v0 of
      C_SemigroupLaws'46'constructor_2433 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.Semigroup.Core._.SemigroupLaws.◇-assocˡ
d_'9671''45'assoc'737'_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_Semigroup_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_ISetoid_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_SetoidLaws_302 ->
  T_SemigroupLaws_40 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'9671''45'assoc'737'_320 ~v0 ~v1 v2 ~v3 v4 v5 v6 v7 v8
  = du_'9671''45'assoc'737'_320 v2 v4 v5 v6 v7 v8
du_'9671''45'assoc'737'_320 ::
  T_Semigroup_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_SetoidLaws_302 ->
  T_SemigroupLaws_40 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'9671''45'assoc'737'_320 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (MAlonzo.Code.Class.Setoid.Core.d_isEquivalence_310 (coe v1))
      (coe d__'9671'__16 v0 (coe d__'9671'__16 v0 v3 v4) v5)
      (coe d__'9671'__16 v0 v3 (coe d__'9671'__16 v0 v4 v5))
      (coe d_'9671''45'assoc'691'_312 v2 v3 v4 v5)
-- Class.Semigroup.Core._.SemigroupLaws≡
d_SemigroupLaws'8801'_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Semigroup_10 -> ()
d_SemigroupLaws'8801'_332 = erased
-- Class.Semigroup.Core._.◇-assocʳ
d_'9671''45'assoc'691'_336 ::
  T_SemigroupLaws_40 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'9671''45'assoc'691'_336 v0
  = coe d_'9671''45'assoc'691'_312 (coe v0)
-- Class.Semigroup.Core._.◇-assocˡ
d_'9671''45'assoc'737'_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_Semigroup_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_ISetoid_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_SetoidLaws_302 ->
  T_SemigroupLaws_40 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'9671''45'assoc'737'_338 ~v0 ~v1 v2 ~v3 v4 v5
  = du_'9671''45'assoc'737'_338 v2 v4 v5
du_'9671''45'assoc'737'_338 ::
  T_Semigroup_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_SetoidLaws_302 ->
  T_SemigroupLaws_40 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'9671''45'assoc'737'_338 v0 v1 v2
  = coe du_'9671''45'assoc'737'_320 (coe v0) (coe v1) (coe v2)
-- Class.Semigroup.Core._.◇-comm
d_'9671''45'comm_340 ::
  T_SemigroupLaws_40 -> AgdaAny -> AgdaAny -> AgdaAny
d_'9671''45'comm_340 v0 = coe d_'9671''45'comm_310 (coe v0)
-- Class.Semigroup.Core._._.◇-assocʳ
d_'9671''45'assoc'691'_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_Semigroup_10 ->
  T_SemigroupLaws_40 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'9671''45'assoc'691'_358 = erased
-- Class.Semigroup.Core._._.◇-assocˡ
d_'9671''45'assoc'737'_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_Semigroup_10 ->
  T_SemigroupLaws_40 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'9671''45'assoc'737'_360 = erased
-- Class.Semigroup.Core._._.◇-comm
d_'9671''45'comm_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  T_Semigroup_10 ->
  T_SemigroupLaws_40 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'9671''45'comm_362 = erased
