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

module MAlonzo.Code.Data.Unit.Polymorphic.Base where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Level qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Unit.Polymorphic.Base.⊤
d_'8868'_10 :: MAlonzo.Code.Agda.Primitive.T_Level_18 -> ()
d_'8868'_10 = erased
-- Data.Unit.Polymorphic.Base.tt
d_tt_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Level.T_Lift_8
d_tt_16 ~v0 = du_tt_16
du_tt_16 :: MAlonzo.Code.Level.T_Lift_8
du_tt_16
  = coe
      MAlonzo.Code.Level.C_lift_20
      (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
