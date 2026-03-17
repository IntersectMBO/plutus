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

module MAlonzo.Code.Class.Monad.Id where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Applicative.Core
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Class.Monad.Core

-- Class.Monad.Id.Id
d_Id_6 :: MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_Id_6 = erased
-- Class.Monad.Id.Functor-Id
d_Functor'45'Id_8 :: MAlonzo.Code.Class.Functor.Core.T_Functor_14
d_Functor'45'Id_8
  = coe
      MAlonzo.Code.Class.Functor.Core.C_Functor'46'constructor_121
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Class.Monad.Id.Applicative-Id
d_Applicative'45'Id_10 ::
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
d_Applicative'45'Id_10
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Applicative'46'constructor_317
      (coe d_Functor'45'Id_8) (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Class.Monad.Id.Monad-Id
d_Monad'45'Id_12 :: MAlonzo.Code.Class.Monad.Core.T_Monad_8
d_Monad'45'Id_12
  = coe
      MAlonzo.Code.Class.Monad.Core.C_Monad'46'constructor_309
      (coe d_Applicative'45'Id_10) (coe (\ v0 v1 v2 -> v2))
      (coe (\ v0 v1 v2 v3 v4 v5 -> coe v5 v4))
