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

module MAlonzo.Code.Data.Empty where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant

-- Data.Empty.Empty
d_Empty_4 = ()
data T_Empty_4
-- Data.Empty.⊥
d_'8869'_6 :: ()
d_'8869'_6 = erased
-- Data.Empty.⊥-elim
d_'8869''45'elim_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8869''45'elim_12 ~v0 ~v1 ~v2 = du_'8869''45'elim_12
du_'8869''45'elim_12 :: AgdaAny
du_'8869''45'elim_12 = MAlonzo.RTE.mazUnreachableError
-- Data.Empty.⊥-elim-irr
d_'8869''45'elim'45'irr_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8869''45'elim'45'irr_18 ~v0 ~v1 ~v2
  = du_'8869''45'elim'45'irr_18
du_'8869''45'elim'45'irr_18 :: AgdaAny
du_'8869''45'elim'45'irr_18 = MAlonzo.RTE.mazUnreachableError
