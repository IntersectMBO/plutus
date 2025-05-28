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

module MAlonzo.Code.Data.Sum where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Level qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Sum._.isInj₁
d_isInj'8321'_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Maybe AgdaAny
d_isInj'8321'_24 ~v0 ~v1 ~v2 ~v3 v4 = du_isInj'8321'_24 v4
du_isInj'8321'_24 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Maybe AgdaAny
du_isInj'8321'_24 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum._.isInj₂
d_isInj'8322'_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Maybe AgdaAny
d_isInj'8322'_30 ~v0 ~v1 ~v2 ~v3 v4 = du_isInj'8322'_30 v4
du_isInj'8322'_30 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> Maybe AgdaAny
du_isInj'8322'_30 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum._.From-inj₁
d_From'45'inj'8321'_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_From'45'inj'8321'_36 = erased
-- Data.Sum._.from-inj₁
d_from'45'inj'8321'_40 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_from'45'inj'8321'_40 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1 -> coe v1
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1
        -> coe
             MAlonzo.Code.Level.C_lift_20
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum._.From-inj₂
d_From'45'inj'8322'_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> ()
d_From'45'inj'8322'_44 = erased
-- Data.Sum._.from-inj₂
d_from'45'inj'8322'_48 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_from'45'inj'8322'_48 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v1
        -> coe
             MAlonzo.Code.Level.C_lift_20
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
