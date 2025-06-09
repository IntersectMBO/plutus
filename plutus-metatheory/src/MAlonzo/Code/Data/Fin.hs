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

module MAlonzo.Code.Data.Fin where

import Data.Text qualified
import MAlonzo.Code.Data.Fin.Base qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Fin.#_
d_'35'__10 ::
  Integer ->
  Integer -> AgdaAny -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_'35'__10 v0 ~v1 ~v2 = du_'35'__10 v0
du_'35'__10 :: Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_'35'__10 v0
  = coe MAlonzo.Code.Data.Fin.Base.du_fromℕ'60'_52 (coe v0)
