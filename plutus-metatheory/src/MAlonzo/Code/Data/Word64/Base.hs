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

module MAlonzo.Code.Data.Word64.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Function.Base

-- Data.Word64.Base.liftOp₂
d_liftOp'8322'_6 ::
  (Integer -> Integer -> Integer) ->
  MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64
d_liftOp'8322'_6 v0
  = coe
      MAlonzo.Code.Function.Base.du__on__334
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8322''8242'__222
         (coe word64FromNat) (coe v0))
      (coe word64ToNat)
-- Data.Word64.Base._≈_
d__'8776'__10 :: MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64 -> ()
d__'8776'__10 = erased
-- Data.Word64.Base._<_
d__'60'__12 :: MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64 -> ()
d__'60'__12 = erased
-- Data.Word64.Base._≤_
d__'8804'__14 :: MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64 -> ()
d__'8804'__14 = erased
