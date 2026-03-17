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

module MAlonzo.Code.Meta.Init where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Class.Monad.Core
import qualified MAlonzo.Code.Class.MonadError
import qualified MAlonzo.Code.Class.MonadReader
import qualified MAlonzo.Code.Class.MonadTC
import qualified MAlonzo.Code.Reflection.TCI

-- Meta.Init.iMonad-TC
d_iMonad'45'TC_4 :: MAlonzo.Code.Class.Monad.Core.T_Monad_8
d_iMonad'45'TC_4 = coe MAlonzo.Code.Reflection.TCI.d_Monad'45'TC_6
-- Meta.Init.iMonadTC-TCI
d_iMonadTC'45'TCI_6 :: MAlonzo.Code.Class.MonadTC.T_MonadTC_80
d_iMonadTC'45'TCI_6
  = coe MAlonzo.Code.Reflection.TCI.d_MonadTC'45'TCI_146
-- Meta.Init.iMonadReader-TC
d_iMonadReader'45'TC_8 ::
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18
d_iMonadReader'45'TC_8
  = coe MAlonzo.Code.Reflection.TCI.d_MonadReader'45'TC_8
-- Meta.Init.iMonadError-TC
d_iMonadError'45'TC_10 ::
  MAlonzo.Code.Class.MonadError.T_MonadError_16
d_iMonadError'45'TC_10
  = coe MAlonzo.Code.Reflection.TCI.d_MonadError'45'TC_12
