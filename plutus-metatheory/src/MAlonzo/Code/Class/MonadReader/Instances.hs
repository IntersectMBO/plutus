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

module MAlonzo.Code.Class.MonadReader.Instances where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Monad.Core
import qualified MAlonzo.Code.Class.MonadReader

-- Class.MonadReader.Instances._.ask
d_ask_8 ::
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 -> AgdaAny
d_ask_8 v0 = coe MAlonzo.Code.Class.MonadReader.d_ask_34 (coe v0)
-- Class.MonadReader.Instances._.local
d_local_10 ::
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_local_10 v0
  = coe MAlonzo.Code.Class.MonadReader.d_local_40 (coe v0)
-- Class.MonadReader.Instances._.reader
d_reader_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny
d_reader_12 v0 ~v1 ~v2 v3 v4 = du_reader_12 v0 v3 v4
du_reader_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.MonadReader.T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny
du_reader_12 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Class.MonadReader.du_reader_46 (coe v0) (coe v1)
      (coe v2) v3 v5
