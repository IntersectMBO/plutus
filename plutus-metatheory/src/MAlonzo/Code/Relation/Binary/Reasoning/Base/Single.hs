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

module MAlonzo.Code.Relation.Binary.Reasoning.Base.Single where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax

-- Relation.Binary.Reasoning.Base.Single._IsRelatedTo_
d__IsRelatedTo__26 a0 a1 a2 a3 a4 a5 a6 a7 = ()
newtype T__IsRelatedTo__26 = C_relTo_34 AgdaAny
-- Relation.Binary.Reasoning.Base.Single.start
d_start_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__26 -> AgdaAny
d_start_36 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 = du_start_36 v8
du_start_36 :: T__IsRelatedTo__26 -> AgdaAny
du_start_36 v0
  = case coe v0 of
      C_relTo_34 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Reasoning.Base.Single.∼-go
d_'8764''45'go_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__26 -> T__IsRelatedTo__26
d_'8764''45'go_40 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10
  = du_'8764''45'go_40 v5 v6 v7 v8 v9 v10
du_'8764''45'go_40 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__26 -> T__IsRelatedTo__26
du_'8764''45'go_40 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      C_relTo_34 v6 -> coe C_relTo_34 (coe v0 v1 v2 v3 v4 v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Reasoning.Base.Single.≡-go
d_'8801''45'go_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__26 -> T__IsRelatedTo__26
d_'8801''45'go_46 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_'8801''45'go_46 v10
du_'8801''45'go_46 :: T__IsRelatedTo__26 -> T__IsRelatedTo__26
du_'8801''45'go_46 v0 = coe v0
-- Relation.Binary.Reasoning.Base.Single..extendedlambda0
d_'46'extendedlambda0_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'46'extendedlambda0_52 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         v10 ~v11
  = du_'46'extendedlambda0_52 v10
du_'46'extendedlambda0_52 :: AgdaAny -> AgdaAny
du_'46'extendedlambda0_52 v0 = coe v0
-- Relation.Binary.Reasoning.Base.Single.stop
d_stop_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T__IsRelatedTo__26
d_stop_54 ~v0 ~v1 ~v2 ~v3 v4 ~v5 v6 = du_stop_54 v4 v6
du_stop_54 :: (AgdaAny -> AgdaAny) -> AgdaAny -> T__IsRelatedTo__26
du_stop_54 v0 v1 = coe C_relTo_34 (coe v0 v1)
-- Relation.Binary.Reasoning.Base.Single._.begin_
d_begin__58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__26 -> AgdaAny
d_begin__58 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_begin__58
du_begin__58 :: AgdaAny -> AgdaAny -> T__IsRelatedTo__26 -> AgdaAny
du_begin__58
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v0 v1 v2 -> coe du_start_36 v2)
-- Relation.Binary.Reasoning.Base.Single._.step-≡
d_step'45''8801'_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__26
d_step'45''8801'_62 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_step'45''8801'_62
du_step'45''8801'_62 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__26
du_step'45''8801'_62
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.Base.Single._.step-≡-∣
d_step'45''8801''45''8739'_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__26 -> T__IsRelatedTo__26
d_step'45''8801''45''8739'_64 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du_step'45''8801''45''8739'_64 v8
du_step'45''8801''45''8739'_64 ::
  T__IsRelatedTo__26 -> T__IsRelatedTo__26
du_step'45''8801''45''8739'_64 v0 = coe v0
-- Relation.Binary.Reasoning.Base.Single._.step-≡-⟨
d_step'45''8801''45''10216'_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__26
d_step'45''8801''45''10216'_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_step'45''8801''45''10216'_66
du_step'45''8801''45''10216'_66 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__26
du_step'45''8801''45''10216'_66
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.Base.Single._.step-≡-⟩
d_step'45''8801''45''10217'_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__26
d_step'45''8801''45''10217'_68 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_step'45''8801''45''10217'_68
du_step'45''8801''45''10217'_68 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__26
du_step'45''8801''45''10217'_68
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.Base.Single._.step-≡˘
d_step'45''8801''728'_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__26
d_step'45''8801''728'_70 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_step'45''8801''728'_70
du_step'45''8801''728'_70 ::
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__26
du_step'45''8801''728'_70
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_454
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Reasoning.Base.Single._.step-∼
d_step'45''8764'_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__26 -> AgdaAny -> T__IsRelatedTo__26
d_step'45''8764'_74 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_step'45''8764'_74 v5
du_step'45''8764'_74 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> T__IsRelatedTo__26 -> AgdaAny -> T__IsRelatedTo__26
du_step'45''8764'_74 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_302
      (coe du_'8764''45'go_40 (coe v0))
-- Relation.Binary.Reasoning.Base.Single._._∎
d__'8718'_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T__IsRelatedTo__26
d__'8718'_78 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8718'_78 v4
du__'8718'_78 ::
  (AgdaAny -> AgdaAny) -> AgdaAny -> T__IsRelatedTo__26
du__'8718'_78 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
      (coe du_stop_54 (coe v0))
