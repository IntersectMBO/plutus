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

module MAlonzo.Code.Class.Applicative.Instances where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Class.Applicative.Core
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Class.Functor.Instances
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.NonEmpty.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Vec.Base

-- Class.Applicative.Instances.Applicative-Maybe
d_Applicative'45'Maybe_6 ::
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
d_Applicative'45'Maybe_6
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Applicative'46'constructor_317
      (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'Maybe_6)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16))
      (coe
         (\ v0 v1 v2 v3 ->
            coe
              MAlonzo.Code.Data.Maybe.Base.du_maybe_32
              (coe
                 MAlonzo.Code.Class.Functor.Core.du_fmap_22
                 MAlonzo.Code.Class.Functor.Instances.d_Functor'45'Maybe_6 v0 erased
                 v2 erased)
              (let v4 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
               coe (coe (\ v5 -> v4)))))
-- Class.Applicative.Instances.Applicative₀-Maybe
d_Applicative'8320''45'Maybe_10 ::
  MAlonzo.Code.Class.Applicative.Core.T_Applicative'8320'_84
d_Applicative'8320''45'Maybe_10
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Applicative'8320''46'constructor_7849
      (coe d_Applicative'45'Maybe_6)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
-- Class.Applicative.Instances.Alternative-Maybe
d_Alternative'45'Maybe_12 ::
  MAlonzo.Code.Class.Applicative.Core.T_Alternative_104
d_Alternative'45'Maybe_12
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Alternative'46'constructor_8035
      (coe
         (\ v0 v1 ->
            coe MAlonzo.Code.Data.Maybe.Base.du__'60''8739''62'__80))
-- Class.Applicative.Instances.Applicative-List
d_Applicative'45'List_18 ::
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
d_Applicative'45'List_18
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Applicative'46'constructor_317
      (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270))
      (coe
         (\ v0 v1 v2 v3 v4 v5 ->
            coe
              MAlonzo.Code.Data.List.Base.du_concatMap_246
              (coe
                 MAlonzo.Code.Class.Functor.Core.du__'60''38''62'__30
                 (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List_92)
                 (coe v0) (coe v2) (coe v5))
              (coe v4)))
-- Class.Applicative.Instances.Applicative₀-List
d_Applicative'8320''45'List_22 ::
  MAlonzo.Code.Class.Applicative.Core.T_Applicative'8320'_84
d_Applicative'8320''45'List_22
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Applicative'8320''46'constructor_7849
      (coe d_Applicative'45'List_18)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Class.Applicative.Instances.Alternative-List
d_Alternative'45'List_24 ::
  MAlonzo.Code.Class.Applicative.Core.T_Alternative_104
d_Alternative'45'List_24
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Alternative'46'constructor_8035
      (coe (\ v0 v1 -> coe MAlonzo.Code.Data.List.Base.du__'43''43'__32))
-- Class.Applicative.Instances.Applicative-List⁺
d_Applicative'45'List'8314'_26 ::
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
d_Applicative'45'List'8314'_26
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Applicative'46'constructor_317
      (coe
         MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List'8314'_140)
      (coe
         (\ v0 v1 ->
            coe MAlonzo.Code.Data.List.NonEmpty.Base.du_'91'_'93'_42))
      (coe
         (\ v0 v1 v2 v3 v4 v5 ->
            coe
              MAlonzo.Code.Data.List.NonEmpty.Base.du_concatMap_208
              (coe
                 MAlonzo.Code.Class.Functor.Core.du__'60''38''62'__30
                 (coe
                    MAlonzo.Code.Class.Functor.Instances.d_Functor'45'List'8314'_140)
                 (coe v0) (coe v2) (coe v5))
              v4))
-- Class.Applicative.Instances.Applicative-Vec
d_Applicative'45'Vec_36 ::
  Integer -> MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
d_Applicative'45'Vec_36 v0
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Applicative'46'constructor_317
      (coe MAlonzo.Code.Class.Functor.Instances.du_Functor'45'Vec_262)
      (coe
         (\ v1 v2 ->
            coe MAlonzo.Code.Data.Vec.Base.du_replicate_444 (coe v0)))
      (coe
         (\ v1 v2 v3 v4 -> coe MAlonzo.Code.Data.Vec.Base.du__'8859'__284))
-- Class.Applicative.Instances.Applicative₀-Vec
d_Applicative'8320''45'Vec_44 ::
  MAlonzo.Code.Class.Applicative.Core.T_Applicative'8320'_84
d_Applicative'8320''45'Vec_44
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Applicative'8320''46'constructor_7849
      (coe d_Applicative'45'Vec_36 (coe (0 :: Integer)))
      (coe (\ v0 v1 -> coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32))
-- Class.Applicative.Instances.Alternative-TC
d_Alternative'45'TC_48 ::
  MAlonzo.Code.Class.Applicative.Core.T_Alternative_104
d_Alternative'45'TC_48
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Alternative'46'constructor_8035
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_catchTC_358)
-- Class.Applicative.Instances.Applicative-TC
d_Applicative'45'TC_50 ::
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
d_Applicative'45'TC_50
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Applicative'46'constructor_317
      (coe MAlonzo.Code.Class.Functor.Instances.d_Functor'45'TC_436)
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326)
      (coe
         (\ v0 v1 v2 v3 v4 v5 ->
            coe
              MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 () v2 erased
              erased v4
              (\ v6 ->
                 coe
                   MAlonzo.Code.Agda.Builtin.Reflection.d_bindTC_336 v0 v2 erased
                   erased v5
                   (\ v7 ->
                      coe
                        MAlonzo.Code.Agda.Builtin.Reflection.d_returnTC_326 v2 erased
                        (coe v6 v7)))))
