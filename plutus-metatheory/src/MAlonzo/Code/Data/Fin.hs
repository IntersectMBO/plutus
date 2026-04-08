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

module MAlonzo.Code.Data.Fin where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Data.Fin.Base

-- Data.Fin.#_
d_'35'__10 ::
  Integer ->
  Integer -> AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_'35'__10 v0 ~v1 ~v2 = du_'35'__10 v0
du_'35'__10 :: Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_'35'__10 v0
  = coe MAlonzo.Code.Data.Fin.Base.du_fromℕ'60'_52 (coe v0)
