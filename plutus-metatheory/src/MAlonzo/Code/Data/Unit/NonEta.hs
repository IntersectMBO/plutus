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

module MAlonzo.Code.Data.Unit.NonEta where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Unit.NonEta.Unit
d_Unit_6 = ()
data T_Unit_6 = C_unit_8
-- Data.Unit.NonEta.Hidden
d_Hidden_12 :: MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_Hidden_12 = erased
-- Data.Unit.NonEta.hide
d_hide_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> T_Unit_6 -> AgdaAny
d_hide_28 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 = du_hide_28 v4 v5
du_hide_28 :: (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_hide_28 v0 v1 = coe v0 v1
-- Data.Unit.NonEta.reveal
d_reveal_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (T_Unit_6 -> AgdaAny) -> AgdaAny
d_reveal_38 ~v0 ~v1 v2 = du_reveal_38 v2
du_reveal_38 :: (T_Unit_6 -> AgdaAny) -> AgdaAny
du_reveal_38 v0 = coe v0 erased
