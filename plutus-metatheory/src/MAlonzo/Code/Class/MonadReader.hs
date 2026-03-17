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

module MAlonzo.Code.Class.MonadReader where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Applicative.Core
import qualified MAlonzo.Code.Class.Functor.Core
import qualified MAlonzo.Code.Class.Monad.Core
import qualified MAlonzo.Code.Class.MonadError

-- Class.MonadReader._.catch
d_catch_6 ::
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_catch_6 v0
  = coe MAlonzo.Code.Class.MonadError.d_catch_28 (coe v0)
-- Class.MonadReader._.error
d_error_8 ::
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> AgdaAny
d_error_8 v0
  = coe MAlonzo.Code.Class.MonadError.d_error_26 (coe v0)
-- Class.MonadReader.MonadReader
d_MonadReader_18 a0 a1 a2 a3 = ()
data T_MonadReader_18
  = C_MonadReader'46'constructor_305 AgdaAny
                                     (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
                                      () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny)
-- Class.MonadReader.MonadReader.ask
d_ask_34 :: T_MonadReader_18 -> AgdaAny
d_ask_34 v0
  = case coe v0 of
      C_MonadReader'46'constructor_305 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadReader.MonadReader.local
d_local_40 ::
  T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_local_40 v0
  = case coe v0 of
      C_MonadReader'46'constructor_305 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Class.MonadReader.MonadReader.reader
d_reader_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny
d_reader_46 v0 ~v1 ~v2 v3 v4 v5 ~v6 v7
  = du_reader_46 v0 v3 v4 v5 v7
du_reader_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) -> AgdaAny
du_reader_46 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20
      (MAlonzo.Code.Class.Applicative.Core.d_super_18
         (coe MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v1)))
      v0 erased v3 erased v4 (d_ask_34 (coe v2))
-- Class.MonadReader._.ask
d_ask_52 :: T_MonadReader_18 -> AgdaAny
d_ask_52 v0 = coe d_ask_34 (coe v0)
-- Class.MonadReader._.local
d_local_54 ::
  T_MonadReader_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_local_54 v0 = coe d_local_40 (coe v0)
-- Class.MonadReader.ReaderT
d_ReaderT_66 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_ReaderT_66 = erased
-- Class.MonadReader._.Functor-ReaderT
d_Functor'45'ReaderT_84 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Functor.Core.T_Functor_14 ->
  MAlonzo.Code.Class.Functor.Core.T_Functor_14
d_Functor'45'ReaderT_84 ~v0 ~v1 v2 = du_Functor'45'ReaderT_84 v2
du_Functor'45'ReaderT_84 ::
  MAlonzo.Code.Class.Functor.Core.T_Functor_14 ->
  MAlonzo.Code.Class.Functor.Core.T_Functor_14
du_Functor'45'ReaderT_84 v0
  = coe
      MAlonzo.Code.Class.Functor.Core.C_Functor'46'constructor_121
      (coe
         (\ v1 v2 v3 v4 v5 v6 v7 ->
            coe
              MAlonzo.Code.Class.Functor.Core.d__'60''36''62'__20 v0 v1 erased v3
              erased v5 (coe v6 v7)))
-- Class.MonadReader._._
d___92 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Functor.Core.T_Functor_14 ->
  MAlonzo.Code.Class.Functor.Core.T_Functor_14
d___92 ~v0 ~v1 = du___92
du___92 ::
  MAlonzo.Code.Class.Functor.Core.T_Functor_14 ->
  MAlonzo.Code.Class.Functor.Core.T_Functor_14
du___92 = coe du_Functor'45'ReaderT_84
-- Class.MonadReader._.Applicative-ReaderT
d_Applicative'45'ReaderT_94 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8 ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
d_Applicative'45'ReaderT_94 ~v0 ~v1 v2
  = du_Applicative'45'ReaderT_94 v2
du_Applicative'45'ReaderT_94 ::
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8 ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
du_Applicative'45'ReaderT_94 v0
  = coe
      MAlonzo.Code.Class.Applicative.Core.C_Applicative'46'constructor_317
      (coe
         du___92 (MAlonzo.Code.Class.Applicative.Core.d_super_18 (coe v0)))
      (coe
         (\ v1 v2 v3 ->
            let v4
                  = coe
                      MAlonzo.Code.Class.Applicative.Core.d_pure_20 v0 v1 erased v3 in
            coe (\ v5 -> v4)))
      (coe
         (\ v1 v2 v3 v4 v5 v6 v7 ->
            coe
              MAlonzo.Code.Class.Applicative.Core.d__'60''42''62'__22 v0 v1
              erased v3 erased (coe v5 v7) (coe v6 v7)))
-- Class.MonadReader._._
d___104 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8 ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
d___104 ~v0 ~v1 = du___104
du___104 ::
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8 ->
  MAlonzo.Code.Class.Applicative.Core.T_Applicative_8
du___104 = coe du_Applicative'45'ReaderT_94
-- Class.MonadReader._.Monad-ReaderT
d_Monad'45'ReaderT_106 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8
d_Monad'45'ReaderT_106 ~v0 ~v1 v2 = du_Monad'45'ReaderT_106 v2
du_Monad'45'ReaderT_106 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8
du_Monad'45'ReaderT_106 v0
  = coe
      MAlonzo.Code.Class.Monad.Core.C_Monad'46'constructor_309
      (coe du___104 (MAlonzo.Code.Class.Monad.Core.d_super_18 (coe v0)))
      (coe
         (\ v1 v2 v3 v4 ->
            coe MAlonzo.Code.Class.Monad.Core.d_return_20 v0 v1 erased v3))
      (coe
         (\ v1 v2 v3 v4 v5 v6 v7 ->
            coe
              MAlonzo.Code.Class.Monad.Core.d__'62''62''61'__22 v0 v1 erased v3
              erased (coe v5 v7) (\ v8 -> coe v6 v8 v7)))
-- Class.MonadReader._.MonadReader-ReaderT
d_MonadReader'45'ReaderT_120 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 -> T_MonadReader_18
d_MonadReader'45'ReaderT_120 ~v0 ~v1 v2
  = du_MonadReader'45'ReaderT_120 v2
du_MonadReader'45'ReaderT_120 ::
  MAlonzo.Code.Class.Monad.Core.T_Monad_8 -> T_MonadReader_18
du_MonadReader'45'ReaderT_120 v0
  = coe
      C_MonadReader'46'constructor_305
      (coe
         (\ v1 ->
            coe MAlonzo.Code.Class.Monad.Core.d_return_20 v0 () erased v1))
      (coe (\ v1 v2 v3 v4 v5 -> coe v4 (coe v3 v5)))
-- Class.MonadReader._.MonadError-ReaderT
d_MonadError'45'ReaderT_132 ::
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16
d_MonadError'45'ReaderT_132 ~v0 ~v1 ~v2 ~v3 v4
  = du_MonadError'45'ReaderT_132 v4
du_MonadError'45'ReaderT_132 ::
  MAlonzo.Code.Class.MonadError.T_MonadError_16 ->
  MAlonzo.Code.Class.MonadError.T_MonadError_16
du_MonadError'45'ReaderT_132 v0
  = coe
      MAlonzo.Code.Class.MonadError.C_MonadError'46'constructor_359
      (coe
         (\ v1 v2 v3 v4 ->
            coe MAlonzo.Code.Class.MonadError.d_error_26 v0 v1 erased v3))
      (coe
         (\ v1 v2 v3 v4 v5 ->
            coe
              MAlonzo.Code.Class.MonadError.d_catch_28 v0 v1 erased (coe v3 v5)
              (\ v6 -> coe v4 v6 v5)))
