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

module MAlonzo.Code.Class.MonadError where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Applicative.Core
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Class.Monad.Core
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base

-- Class.MonadError.MonadError
d_MonadError_16 a0 a1 a2 = ()
data T_MonadError_16
  = C_MonadError'46'constructor_359 (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                     () -> AgdaAny -> AgdaAny)
                                    (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                     () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
-- Class.MonadError.MonadError.error
d_error_26 ::
  T_MonadError_16 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_error_26 v0
  = case coe v0 of
      C_MonadError'46'constructor_359 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadError.MonadError.catch
d_catch_28 ::
  T_MonadError_16 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_catch_28 v0
  = case coe v0 of
      C_MonadError'46'constructor_359 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadError.MonadError-TC
d_MonadError'45'TC_30 :: T_MonadError_16
d_MonadError'45'TC_30
  = coe
      C_MonadError'46'constructor_359
      (coe
         (\ v0 v1 ->
            coe
              MAlonzo.Code.Agda.Builtin.Reflection.d_typeError_344 v0 erased))
      (coe
         (\ v0 v1 v2 v3 ->
            coe
              MAlonzo.Code.Agda.Builtin.Reflection.d_catchTC_358 v0 erased v2
              (coe
                 v3
                 (coe
                    MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                    (coe
                       MAlonzo.Code.Agda.Builtin.Reflection.C_strErr_310
                       (coe
                          ("TC doesn't provide which error to catch" :: Data.Text.Text)))))))
-- Class.MonadError.ErrorT
d_ErrorT_44 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_ErrorT_44 = erased
-- Class.MonadError._.Functor-ErrorT
d_Functor'45'ErrorT_64 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Functor.Core.T_Functor_14 ->
  MAlonzo.Code.Class.Functor.Core.T_Functor_14
d_Functor'45'ErrorT_64 ~v0 ~v1 v2 = du_Functor'45'ErrorT_64 v2
du_Functor'45'ErrorT_64 ::
  MAlonzo.Code.Class.Functor.Core.T_Functor_14 ->
  MAlonzo.Code.Class.Functor.Core.T_Functor_14
du_Functor'45'ErrorT_64 v0
  = coe
      MAlonzo.Code.Class.Functor.Core.C_Functor'46'constructor_121
      (coe
         (\ v1 v2 v3 v4 v5 ->
            coe
              MAlonzo.Code.Class.Functor.Core.du_fmap_22 v0 v1 erased v3 erased
              (coe MAlonzo.Code.Data.Sum.Base.du_map'8322'_94 v5)))
-- Class.MonadError._._
d___68 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Functor.Core.T_Functor_14 ->
  MAlonzo.Code.Class.Functor.Core.T_Functor_14
d___68 ~v0 ~v1 = du___68
du___68 ::
  MAlonzo.Code.Class.Functor.Core.T_Functor_14 ->
  MAlonzo.Code.Class.Functor.Core.T_Functor_14
du___68 = coe du_Functor'45'ErrorT_64
-- Class.MonadError._.Applicative-ErrorT
d_Applicative'45'ErrorT_72 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8 ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
d_Applicative'45'ErrorT_72 ~v0 ~v1 v2
  = du_Applicative'45'ErrorT_72 v2
du_Applicative'45'ErrorT_72 ::
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8 ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
du_Applicative'45'ErrorT_72 v0
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Applicative'46'constructor_317
      (coe
         du___68 (MAlonzo.Code.Class.Applicative.Core.d_super_18 (coe v0)))
      (coe
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Class.Applicative.Core.d_pure_20 v0 v1 erased
              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3))))
      (coe
         (\ v1 v2 v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Class.Applicative.Core.d__'60''42''62'__22 v0 v1
              erased v3 erased
              (coe
                 MAlonzo.Code.Class.Functor.Core.du_fmap_22
                 (MAlonzo.Code.Class.Applicative.Core.d_super_18 (coe v0)) () erased
                 () erased (coe du_go_84) v5)
              v6))
-- Class.MonadError._._.go
d_go_84 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_go_84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 v13
        v14
  = du_go_84 v13 v14
du_go_84 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_go_84 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v0
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v1
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
               -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v2 v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadError._._
d___96 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8 ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
d___96 ~v0 ~v1 = du___96
du___96 ::
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8 ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
du___96 = coe du_Applicative'45'ErrorT_72
-- Class.MonadError._.Monad-ErrorT
d_Monad'45'ErrorT_100 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8
d_Monad'45'ErrorT_100 ~v0 ~v1 v2 = du_Monad'45'ErrorT_100 v2
du_Monad'45'ErrorT_100 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8
du_Monad'45'ErrorT_100 v0
  = coe
      MAlonzo.Code.Class.Monad.Core.C_Monad'46'constructor_309
      (coe du___96 (MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
      (coe
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Class.Monad.Core.d_return_20 v0 v1 erased
              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3))))
      (coe
         (\ v1 v2 v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 v1 erased v3
              erased v5
              (\ v7 ->
                 case coe v7 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
                     -> coe MAlonzo.Code.Class.Monad.Core.d_return_20 v0 v3 erased v7
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8 -> coe v6 v8
                   _ -> MAlonzo.RTE.mazUnreachableError)))
-- Class.MonadError._.MonadError-ErrorT
d_MonadError'45'ErrorT_118 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 -> T_MonadError_16
d_MonadError'45'ErrorT_118 ~v0 ~v1 v2
  = du_MonadError'45'ErrorT_118 v2
du_MonadError'45'ErrorT_118 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 -> T_MonadError_16
du_MonadError'45'ErrorT_118 v0
  = coe
      C_MonadError'46'constructor_359
      (coe
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Class.Monad.Core.d_return_20 v0 v1 erased
              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v3))))
      (coe
         (\ v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 v1 erased v1
              erased v3
              (coe
                 MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52 (coe v4)
                 (coe
                    (\ v5 ->
                       coe
                         MAlonzo.Code.Class.Monad.Core.d_return_20 v0 v1 erased
                         (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v5)))))))
