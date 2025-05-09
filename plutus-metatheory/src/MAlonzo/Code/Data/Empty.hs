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

module MAlonzo.Code.Data.Empty where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Empty.Empty
d_Empty_4 = ()
data T_Empty_4
-- Data.Empty.⊥
d_'8869'_6 :: ()
d_'8869'_6 = erased
-- Data.Empty.⊥-elim
d_'8869''45'elim_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8869''45'elim_14 ~v0 ~v1 ~v2 = du_'8869''45'elim_14
du_'8869''45'elim_14 :: AgdaAny
du_'8869''45'elim_14 = MAlonzo.RTE.mazUnreachableError
-- Data.Empty.⊥-elim-irr
d_'8869''45'elim'45'irr_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8869''45'elim'45'irr_20 ~v0 ~v1 ~v2
  = du_'8869''45'elim'45'irr_20
du_'8869''45'elim'45'irr_20 :: AgdaAny
du_'8869''45'elim'45'irr_20 = MAlonzo.RTE.mazUnreachableError
