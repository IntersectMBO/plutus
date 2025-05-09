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

module MAlonzo.Code.Algebra.Consequences.Base where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Consequences.Base._.sel⇒idem
d_sel'8658'idem_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny
d_sel'8658'idem_20 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_sel'8658'idem_20 v5 v6
du_sel'8658'idem_20 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny
du_sel'8658'idem_20 v0 v1
  = coe MAlonzo.Code.Data.Sum.Base.du_reduce_76 (coe v0 v1 v1)
-- Algebra.Consequences.Base._.reflexive∧selfInverse⇒involutive
d_reflexive'8743'selfInverse'8658'involutive_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_reflexive'8743'selfInverse'8658'involutive_36 ~v0 ~v1 ~v2 v3 ~v4
                                                v5 v6 v7
  = du_reflexive'8743'selfInverse'8658'involutive_36 v3 v5 v6 v7
du_reflexive'8743'selfInverse'8658'involutive_36 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_reflexive'8743'selfInverse'8658'involutive_36 v0 v1 v2 v3
  = coe v2 v3 (coe v0 v3) (coe v1 (coe v0 v3))
-- Algebra.Consequences.Base.reflexive+selfInverse⇒involutive
d_reflexive'43'selfInverse'8658'involutive_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_reflexive'43'selfInverse'8658'involutive_42 ~v0 ~v1
  = du_reflexive'43'selfInverse'8658'involutive_42
du_reflexive'43'selfInverse'8658'involutive_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_reflexive'43'selfInverse'8658'involutive_42 v0 v1 v2 v3 v4 v5
  = coe du_reflexive'8743'selfInverse'8658'involutive_36 v1 v3 v4 v5
