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

module MAlonzo.Code.Class.Monad.Instances where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Class.Applicative.Instances
import qualified MAlonzo.Code.Class.Monad.Core
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base

-- Class.Monad.Instances.Monad-TC
d_Monad'45'TC_6 :: MAlonzo.Code.Class.Monad.Core.T_Monad_8
d_Monad'45'TC_6
  = coe
      MAlonzo.Code.Class.Monad.Core.C_Monad'46'constructor_309
      (coe
         MAlonzo.Code.Class.Applicative.Instances.d_Applicative'45'TC_50)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326)
      (coe
         (\ v0 v1 v2 ->
            coe
              MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 v0 v2 erased))
-- Class.Monad.Instances.Monad-List
d_Monad'45'List_12 :: MAlonzo.Code.Class.Monad.Core.T_Monad_8
d_Monad'45'List_12
  = coe
      MAlonzo.Code.Class.Monad.Core.C_Monad'46'constructor_309
      (coe
         MAlonzo.Code.Class.Applicative.Instances.d_Applicative'45'List_18)
      (coe
         (\ v0 v1 v2 ->
            coe
              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
      (coe
         (\ v0 v1 v2 v3 v4 v5 ->
            coe
              MAlonzo.Code.Data.List.Base.du_concatMap_246 (coe v5) (coe v4)))
-- Class.Monad.Instances.Monad-Maybe
d_Monad'45'Maybe_18 :: MAlonzo.Code.Class.Monad.Core.T_Monad_8
d_Monad'45'Maybe_18
  = coe
      MAlonzo.Code.Class.Monad.Core.C_Monad'46'constructor_309
      (coe
         MAlonzo.Code.Class.Applicative.Instances.d_Applicative'45'Maybe_6)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16))
      (coe
         (\ v0 v1 v2 v3 ->
            coe MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72))
-- Class.Monad.Instances.MonadLaws-Maybe
d_MonadLaws'45'Maybe_26 ::
  MAlonzo.Code.Class.Monad.Core.T_MonadLaws_164
d_MonadLaws'45'Maybe_26 = erased
