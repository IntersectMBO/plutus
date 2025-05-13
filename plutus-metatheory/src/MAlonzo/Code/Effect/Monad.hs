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

module MAlonzo.Code.Effect.Monad where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Bool.Base qualified
import MAlonzo.Code.Effect.Applicative qualified
import MAlonzo.Code.Effect.Choice qualified
import MAlonzo.Code.Effect.Empty qualified
import MAlonzo.Code.Effect.Functor qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Level qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Effect.Monad.RawMonad
d_RawMonad_24 a0 a1 a2 = ()
data T_RawMonad_24
  = C_RawMonad'46'constructor_319 MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
                                  (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
-- Effect.Monad.RawMonad.rawApplicative
d_rawApplicative_32 ::
  T_RawMonad_24 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_rawApplicative_32 v0
  = case coe v0 of
      C_RawMonad'46'constructor_319 v1 v2 -> coe v1
      _                                   -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonad._>>=_
d__'62''62''61'__34 ::
  T_RawMonad_24 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__34 v0
  = case coe v0 of
      C_RawMonad'46'constructor_319 v1 v2 -> coe v2
      _                                   -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonad._._*>_
d__'42''62'__38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__38 ~v0 ~v1 ~v2 v3 = du__'42''62'__38 v3
du__'42''62'__38 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__38 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Applicative.du__'42''62'__52
      (coe d_rawApplicative_32 (coe v0)) v3 v4
-- Effect.Monad.RawMonad._._<$_
d__'60''36'__40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__40 ~v0 ~v1 ~v2 v3 = du__'60''36'__40 v3
du__'60''36'__40 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__40 v0
  = let v1 = d_rawApplicative_32 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Functor.du__'60''36'__32
           (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v1)) v4
           v5)
-- Effect.Monad.RawMonad._._<$>_
d__'60''36''62'__42 ::
  T_RawMonad_24 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__42 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe
         MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
         (coe d_rawApplicative_32 (coe v0)))
-- Effect.Monad.RawMonad._._<&>_
d__'60''38''62'__44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__44 ~v0 ~v1 ~v2 v3 = du__'60''38''62'__44 v3
du__'60''38''62'__44 ::
  T_RawMonad_24 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__44 v0
  = let v1 = d_rawApplicative_32 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
           (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v1)) v4
           v5)
-- Effect.Monad.RawMonad._._<*_
d__'60''42'__46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__46 ~v0 ~v1 ~v2 v3 = du__'60''42'__46 v3
du__'60''42'__46 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__46 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Applicative.du__'60''42'__46
      (coe d_rawApplicative_32 (coe v0)) v3 v4
-- Effect.Monad.RawMonad._._<*>_
d__'60''42''62'__48 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__48 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d__'60''42''62'__34
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.RawMonad._._<⊛_
d__'60''8859'__50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__50 ~v0 ~v1 ~v2 v3 = du__'60''8859'__50 v3
du__'60''8859'__50 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__50 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du__'60''8859'__72
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.RawMonad._._⊗_
d__'8855'__52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__52 ~v0 ~v1 ~v2 v3 = du__'8855'__52 v3
du__'8855'__52 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__52 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du__'8855'__76
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.RawMonad._._⊛_
d__'8859'__54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__54 ~v0 ~v1 ~v2 v3 = du__'8859'__54 v3
du__'8859'__54 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__54 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du__'8859'__70
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.RawMonad._._⊛>_
d__'8859''62'__56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__56 ~v0 ~v1 ~v2 v3 = du__'8859''62'__56 v3
du__'8859''62'__56 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__56 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du__'8859''62'__74
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.RawMonad._.ignore
d_ignore_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
d_ignore_58 ~v0 ~v1 ~v2 v3 = du_ignore_58 v3
du_ignore_58 :: T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
du_ignore_58 v0
  = let v1 = d_rawApplicative_32 (coe v0) in
    coe
      (\ v2 ->
         coe
           MAlonzo.Code.Effect.Functor.du_ignore_40
           (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v1)))
-- Effect.Monad.RawMonad._.pure
d_pure_60 :: T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
d_pure_60 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_pure_32
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.RawMonad._.rawFunctor
d_rawFunctor_62 ::
  T_RawMonad_24 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_62 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.RawMonad._.return
d_return_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
d_return_64 ~v0 ~v1 ~v2 v3 = du_return_64 v3
du_return_64 :: T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
du_return_64 v0 v1
  = coe
      MAlonzo.Code.Effect.Applicative.du_return_68
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.RawMonad._.zip
d_zip_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_66 ~v0 ~v1 ~v2 v3 = du_zip_66 v3
du_zip_66 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_66 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du_zip_66
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.RawMonad._.zipWith
d_zipWith_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_68 ~v0 ~v1 ~v2 v3 = du_zipWith_68 v3
du_zipWith_68 ::
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_68 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Effect.Applicative.du_zipWith_58
      (coe d_rawApplicative_32 (coe v0)) v4 v5 v6
-- Effect.Monad.RawMonad._>>_
d__'62''62'__70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__70 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du__'62''62'__70 v3
du__'62''62'__70 :: T_RawMonad_24 -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__70 v0
  = coe
      MAlonzo.Code.Effect.Applicative.du__'42''62'__52
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.RawMonad._=<<_
d__'61''60''60'__72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'61''60''60'__72 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du__'61''60''60'__72 v3 v6 v7
du__'61''60''60'__72 ::
  T_RawMonad_24 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'61''60''60'__72 v0 v1 v2
  = coe d__'62''62''61'__34 v0 erased erased v2 v1
-- Effect.Monad.RawMonad.Kleisli
d_Kleisli_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> () -> () -> ()
d_Kleisli_74 = erased
-- Effect.Monad.RawMonad._>=>_
d__'62''61''62'__80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'62''61''62'__80 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du__'62''61''62'__80 v3 v7 v8 v9
du__'62''61''62'__80 ::
  T_RawMonad_24 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'62''61''62'__80 v0 v1 v2 v3
  = coe d__'62''62''61'__34 v0 erased erased (coe v1 v3) v2
-- Effect.Monad.RawMonad._<=<_
d__'60''61''60'__88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''61''60'__88 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8
  = du__'60''61''60'__88 v3 v7 v8
du__'60''61''60'__88 ::
  T_RawMonad_24 ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''61''60'__88 v0 v1 v2
  = coe du__'62''61''62'__80 (coe v0) (coe v2) (coe v1)
-- Effect.Monad.RawMonad.when
d_when_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> Bool -> AgdaAny -> AgdaAny
d_when_90 ~v0 ~v1 ~v2 v3 v4 v5 = du_when_90 v3 v4 v5
du_when_90 :: T_RawMonad_24 -> Bool -> AgdaAny -> AgdaAny
du_when_90 v0 v1 v2
  = if coe v1
      then coe v2
      else coe
             MAlonzo.Code.Effect.Applicative.d_pure_32
             (d_rawApplicative_32 (coe v0)) erased
             (coe
                MAlonzo.Code.Level.C_lift_20
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Effect.Monad.RawMonad.unless
d_unless_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> Bool -> AgdaAny -> AgdaAny
d_unless_96 ~v0 ~v1 ~v2 v3 = du_unless_96 v3
du_unless_96 :: T_RawMonad_24 -> Bool -> AgdaAny -> AgdaAny
du_unless_96 v0
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe du_when_90 (coe v0))
      (coe MAlonzo.Code.Data.Bool.Base.d_not_22)
-- Effect.Monad.Join._._*>_
d__'42''62'__108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__108 ~v0 ~v1 v2 = du__'42''62'__108 v2
du__'42''62'__108 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__108 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Applicative.du__'42''62'__52
      (coe d_rawApplicative_32 (coe v0)) v3 v4
-- Effect.Monad.Join._._<$_
d__'60''36'__110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__110 ~v0 ~v1 v2 = du__'60''36'__110 v2
du__'60''36'__110 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__110 v0
  = let v1 = d_rawApplicative_32 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Functor.du__'60''36'__32
           (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v1)) v4
           v5)
-- Effect.Monad.Join._._<$>_
d__'60''36''62'__112 ::
  T_RawMonad_24 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__112 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe
         MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
         (coe d_rawApplicative_32 (coe v0)))
-- Effect.Monad.Join._._<&>_
d__'60''38''62'__114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__114 ~v0 ~v1 v2 = du__'60''38''62'__114 v2
du__'60''38''62'__114 ::
  T_RawMonad_24 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__114 v0
  = let v1 = d_rawApplicative_32 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
           (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v1)) v4
           v5)
-- Effect.Monad.Join._._<*_
d__'60''42'__116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__116 ~v0 ~v1 v2 = du__'60''42'__116 v2
du__'60''42'__116 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__116 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Applicative.du__'60''42'__46
      (coe d_rawApplicative_32 (coe v0)) v3 v4
-- Effect.Monad.Join._._<*>_
d__'60''42''62'__118 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__118 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d__'60''42''62'__34
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._._<=<_
d__'60''61''60'__120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''61''60'__120 ~v0 ~v1 v2 = du__'60''61''60'__120 v2
du__'60''61''60'__120 ::
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''61''60'__120 v0 v1 v2 v3 v4 v5
  = coe du__'60''61''60'__88 (coe v0) v4 v5
-- Effect.Monad.Join._._<⊛_
d__'60''8859'__122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__122 ~v0 ~v1 v2 = du__'60''8859'__122 v2
du__'60''8859'__122 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__122 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du__'60''8859'__72
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._._=<<_
d__'61''60''60'__124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'61''60''60'__124 ~v0 ~v1 v2 = du__'61''60''60'__124 v2
du__'61''60''60'__124 ::
  T_RawMonad_24 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'61''60''60'__124 v0 v1 v2 v3 v4
  = coe du__'61''60''60'__72 (coe v0) v3 v4
-- Effect.Monad.Join._._>=>_
d__'62''61''62'__126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'62''61''62'__126 ~v0 ~v1 v2 = du__'62''61''62'__126 v2
du__'62''61''62'__126 ::
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'62''61''62'__126 v0 v1 v2 v3 v4 v5 v6
  = coe du__'62''61''62'__80 (coe v0) v4 v5 v6
-- Effect.Monad.Join._._>>_
d__'62''62'__128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__128 ~v0 ~v1 v2 = du__'62''62'__128 v2
du__'62''62'__128 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__128 v0 v1 v2 = coe du__'62''62'__70 (coe v0)
-- Effect.Monad.Join._._>>=_
d__'62''62''61'__130 ::
  T_RawMonad_24 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__130 v0 = coe d__'62''62''61'__34 (coe v0)
-- Effect.Monad.Join._._⊗_
d__'8855'__132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__132 ~v0 ~v1 v2 = du__'8855'__132 v2
du__'8855'__132 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__132 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du__'8855'__76
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._._⊛_
d__'8859'__134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__134 ~v0 ~v1 v2 = du__'8859'__134 v2
du__'8859'__134 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__134 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du__'8859'__70
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._._⊛>_
d__'8859''62'__136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__136 ~v0 ~v1 v2 = du__'8859''62'__136 v2
du__'8859''62'__136 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__136 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du__'8859''62'__74
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._.Kleisli
d_Kleisli_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> () -> () -> ()
d_Kleisli_138 = erased
-- Effect.Monad.Join._.ignore
d_ignore_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
d_ignore_140 ~v0 ~v1 v2 = du_ignore_140 v2
du_ignore_140 :: T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
du_ignore_140 v0
  = let v1 = d_rawApplicative_32 (coe v0) in
    coe
      (\ v2 ->
         coe
           MAlonzo.Code.Effect.Functor.du_ignore_40
           (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v1)))
-- Effect.Monad.Join._.pure
d_pure_142 :: T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
d_pure_142 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_pure_32
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._.rawApplicative
d_rawApplicative_144 ::
  T_RawMonad_24 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_rawApplicative_144 v0 = coe d_rawApplicative_32 (coe v0)
-- Effect.Monad.Join._.rawFunctor
d_rawFunctor_146 ::
  T_RawMonad_24 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_146 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._.return
d_return_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
d_return_148 ~v0 ~v1 v2 = du_return_148 v2
du_return_148 :: T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
du_return_148 v0 v1
  = coe
      MAlonzo.Code.Effect.Applicative.du_return_68
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._.unless
d_unless_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> Bool -> AgdaAny -> AgdaAny
d_unless_150 ~v0 ~v1 v2 = du_unless_150 v2
du_unless_150 :: T_RawMonad_24 -> Bool -> AgdaAny -> AgdaAny
du_unless_150 v0 = coe du_unless_96 (coe v0)
-- Effect.Monad.Join._.when
d_when_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> Bool -> AgdaAny -> AgdaAny
d_when_152 ~v0 ~v1 v2 = du_when_152 v2
du_when_152 :: T_RawMonad_24 -> Bool -> AgdaAny -> AgdaAny
du_when_152 v0 = coe du_when_90 (coe v0)
-- Effect.Monad.Join._.zip
d_zip_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_154 ~v0 ~v1 v2 = du_zip_154 v2
du_zip_154 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_154 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du_zip_66
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._.zipWith
d_zipWith_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_156 ~v0 ~v1 v2 = du_zipWith_156 v2
du_zipWith_156 ::
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_156 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Effect.Applicative.du_zipWith_58
      (coe d_rawApplicative_32 (coe v0)) v4 v5 v6
-- Effect.Monad.Join.join
d_join_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
d_join_158 ~v0 ~v1 v2 ~v3 v4 = du_join_158 v2 v4
du_join_158 :: T_RawMonad_24 -> AgdaAny -> AgdaAny
du_join_158 v0 v1
  = coe d__'62''62''61'__34 v0 erased erased v1 (\ v2 -> v2)
-- Effect.Monad._.mkRawMonad
d_mkRawMonad_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> AgdaAny -> AgdaAny) ->
  (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  T_RawMonad_24
d_mkRawMonad_178 ~v0 ~v1 ~v2 v3 v4 = du_mkRawMonad_178 v3 v4
du_mkRawMonad_178 ::
  (() -> AgdaAny -> AgdaAny) ->
  (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  T_RawMonad_24
du_mkRawMonad_178 v0 v1
  = coe
      C_RawMonad'46'constructor_319
      (let v2
             = coe
                 MAlonzo.Code.Effect.Applicative.du_mkRawApplicative_94 (coe v0) in
       coe
         (coe
            v2
            (\ v3 v4 v5 v6 ->
               coe
                 v1 () v4 v5
                 (\ v7 -> coe v1 v3 v4 v6 (\ v8 -> coe v0 v4 (coe v7 v8))))))
      (coe (\ v2 v3 -> coe v1 v2 v3))
-- Effect.Monad.RawMonadZero
d_RawMonadZero_206 a0 a1 a2 = ()
data T_RawMonadZero_206
  = C_RawMonadZero'46'constructor_7131 T_RawMonad_24
                                       MAlonzo.Code.Effect.Empty.T_RawEmpty_16
-- Effect.Monad.RawMonadZero.rawMonad
d_rawMonad_214 :: T_RawMonadZero_206 -> T_RawMonad_24
d_rawMonad_214 v0
  = case coe v0 of
      C_RawMonadZero'46'constructor_7131 v1 v2 -> coe v1
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonadZero.rawEmpty
d_rawEmpty_216 ::
  T_RawMonadZero_206 -> MAlonzo.Code.Effect.Empty.T_RawEmpty_16
d_rawEmpty_216 v0
  = case coe v0 of
      C_RawMonadZero'46'constructor_7131 v1 v2 -> coe v2
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonadZero._._*>_
d__'42''62'__220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__220 ~v0 ~v1 ~v2 v3 = du__'42''62'__220 v3
du__'42''62'__220 ::
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__220 v0
  = let v1 = d_rawMonad_214 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'42''62'__52
           (coe d_rawApplicative_32 (coe v1)) v4 v5)
-- Effect.Monad.RawMonadZero._._<$_
d__'60''36'__222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__222 ~v0 ~v1 ~v2 v3 = du__'60''36'__222 v3
du__'60''36'__222 ::
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__222 v0
  = let v1 = d_rawMonad_214 (coe v0) in
    coe
      (let v2 = d_rawApplicative_32 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Functor.du__'60''36'__32
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v2)) v5
              v6))
-- Effect.Monad.RawMonadZero._._<$>_
d__'60''36''62'__224 ::
  T_RawMonadZero_206 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__224 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe
         MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
         (coe d_rawApplicative_32 (coe d_rawMonad_214 (coe v0))))
-- Effect.Monad.RawMonadZero._._<&>_
d__'60''38''62'__226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__226 ~v0 ~v1 ~v2 v3 = du__'60''38''62'__226 v3
du__'60''38''62'__226 ::
  T_RawMonadZero_206 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__226 v0
  = let v1 = d_rawMonad_214 (coe v0) in
    coe
      (let v2 = d_rawApplicative_32 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v2)) v5
              v6))
-- Effect.Monad.RawMonadZero._._<*_
d__'60''42'__228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__228 ~v0 ~v1 ~v2 v3 = du__'60''42'__228 v3
du__'60''42'__228 ::
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__228 v0
  = let v1 = d_rawMonad_214 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'60''42'__46
           (coe d_rawApplicative_32 (coe v1)) v4 v5)
-- Effect.Monad.RawMonadZero._._<*>_
d__'60''42''62'__230 ::
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__230 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d__'60''42''62'__34
      (coe d_rawApplicative_32 (coe d_rawMonad_214 (coe v0)))
-- Effect.Monad.RawMonadZero._._<=<_
d__'60''61''60'__232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''61''60'__232 ~v0 ~v1 ~v2 v3 = du__'60''61''60'__232 v3
du__'60''61''60'__232 ::
  T_RawMonadZero_206 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''61''60'__232 v0 v1 v2 v3 v4 v5
  = coe du__'60''61''60'__88 (coe d_rawMonad_214 (coe v0)) v4 v5
-- Effect.Monad.RawMonadZero._._<⊛_
d__'60''8859'__234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__234 ~v0 ~v1 ~v2 v3 = du__'60''8859'__234 v3
du__'60''8859'__234 ::
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__234 v0
  = let v1 = d_rawMonad_214 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'60''8859'__72
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadZero._._=<<_
d__'61''60''60'__236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'61''60''60'__236 ~v0 ~v1 ~v2 v3 = du__'61''60''60'__236 v3
du__'61''60''60'__236 ::
  T_RawMonadZero_206 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'61''60''60'__236 v0 v1 v2 v3 v4
  = coe du__'61''60''60'__72 (coe d_rawMonad_214 (coe v0)) v3 v4
-- Effect.Monad.RawMonadZero._._>=>_
d__'62''61''62'__238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'62''61''62'__238 ~v0 ~v1 ~v2 v3 = du__'62''61''62'__238 v3
du__'62''61''62'__238 ::
  T_RawMonadZero_206 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'62''61''62'__238 v0 v1 v2 v3 v4 v5 v6
  = coe du__'62''61''62'__80 (coe d_rawMonad_214 (coe v0)) v4 v5 v6
-- Effect.Monad.RawMonadZero._._>>_
d__'62''62'__240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__240 ~v0 ~v1 ~v2 v3 = du__'62''62'__240 v3
du__'62''62'__240 ::
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__240 v0 v1 v2
  = coe du__'62''62'__70 (coe d_rawMonad_214 (coe v0))
-- Effect.Monad.RawMonadZero._._>>=_
d__'62''62''61'__242 ::
  T_RawMonadZero_206 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__242 v0
  = coe d__'62''62''61'__34 (coe d_rawMonad_214 (coe v0))
-- Effect.Monad.RawMonadZero._._⊗_
d__'8855'__244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__244 ~v0 ~v1 ~v2 v3 = du__'8855'__244 v3
du__'8855'__244 ::
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__244 v0
  = let v1 = d_rawMonad_214 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8855'__76
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadZero._._⊛_
d__'8859'__246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__246 ~v0 ~v1 ~v2 v3 = du__'8859'__246 v3
du__'8859'__246 ::
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__246 v0
  = let v1 = d_rawMonad_214 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8859'__70
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadZero._._⊛>_
d__'8859''62'__248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__248 ~v0 ~v1 ~v2 v3 = du__'8859''62'__248 v3
du__'8859''62'__248 ::
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__248 v0
  = let v1 = d_rawMonad_214 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8859''62'__74
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadZero._.Kleisli
d_Kleisli_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadZero_206 -> () -> () -> ()
d_Kleisli_250 = erased
-- Effect.Monad.RawMonadZero._.ignore
d_ignore_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadZero_206 -> () -> AgdaAny -> AgdaAny
d_ignore_252 ~v0 ~v1 ~v2 v3 = du_ignore_252 v3
du_ignore_252 :: T_RawMonadZero_206 -> () -> AgdaAny -> AgdaAny
du_ignore_252 v0
  = let v1 = d_rawMonad_214 (coe v0) in
    coe
      (let v2 = d_rawApplicative_32 (coe v1) in
       coe
         (\ v3 ->
            coe
              MAlonzo.Code.Effect.Functor.du_ignore_40
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v2))))
-- Effect.Monad.RawMonadZero._.pure
d_pure_254 :: T_RawMonadZero_206 -> () -> AgdaAny -> AgdaAny
d_pure_254 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_pure_32
      (coe d_rawApplicative_32 (coe d_rawMonad_214 (coe v0)))
-- Effect.Monad.RawMonadZero._.rawApplicative
d_rawApplicative_256 ::
  T_RawMonadZero_206 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_rawApplicative_256 v0
  = coe d_rawApplicative_32 (coe d_rawMonad_214 (coe v0))
-- Effect.Monad.RawMonadZero._.rawFunctor
d_rawFunctor_258 ::
  T_RawMonadZero_206 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_258 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
      (coe d_rawApplicative_32 (coe d_rawMonad_214 (coe v0)))
-- Effect.Monad.RawMonadZero._.return
d_return_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadZero_206 -> () -> AgdaAny -> AgdaAny
d_return_260 ~v0 ~v1 ~v2 v3 = du_return_260 v3
du_return_260 :: T_RawMonadZero_206 -> () -> AgdaAny -> AgdaAny
du_return_260 v0
  = let v1 = d_rawMonad_214 (coe v0) in
    coe
      (\ v2 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_return_68
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadZero._.unless
d_unless_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadZero_206 -> Bool -> AgdaAny -> AgdaAny
d_unless_262 ~v0 ~v1 ~v2 v3 = du_unless_262 v3
du_unless_262 :: T_RawMonadZero_206 -> Bool -> AgdaAny -> AgdaAny
du_unless_262 v0 = coe du_unless_96 (coe d_rawMonad_214 (coe v0))
-- Effect.Monad.RawMonadZero._.when
d_when_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadZero_206 -> Bool -> AgdaAny -> AgdaAny
d_when_264 ~v0 ~v1 ~v2 v3 = du_when_264 v3
du_when_264 :: T_RawMonadZero_206 -> Bool -> AgdaAny -> AgdaAny
du_when_264 v0 = coe du_when_90 (coe d_rawMonad_214 (coe v0))
-- Effect.Monad.RawMonadZero._.zip
d_zip_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_266 ~v0 ~v1 ~v2 v3 = du_zip_266 v3
du_zip_266 ::
  T_RawMonadZero_206 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_266 v0
  = let v1 = d_rawMonad_214 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_zip_66
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadZero._.zipWith
d_zipWith_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_268 ~v0 ~v1 ~v2 v3 = du_zipWith_268 v3
du_zipWith_268 ::
  T_RawMonadZero_206 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_268 v0
  = let v1 = d_rawMonad_214 (coe v0) in
    coe
      (\ v2 v3 v4 v5 v6 v7 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_zipWith_58
           (coe d_rawApplicative_32 (coe v1)) v5 v6 v7)
-- Effect.Monad.RawMonadZero._.empty
d_empty_272 :: T_RawMonadZero_206 -> () -> AgdaAny
d_empty_272 v0
  = coe
      MAlonzo.Code.Effect.Empty.d_empty_22 (coe d_rawEmpty_216 (coe v0))
-- Effect.Monad.RawMonadZero._.∅
d_'8709'_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadZero_206 -> () -> AgdaAny
d_'8709'_274 ~v0 ~v1 ~v2 v3 = du_'8709'_274 v3
du_'8709'_274 :: T_RawMonadZero_206 -> () -> AgdaAny
du_'8709'_274 v0 v1
  = coe
      MAlonzo.Code.Effect.Empty.du_'8709'_24
      (coe d_rawEmpty_216 (coe v0))
-- Effect.Monad.RawMonadZero.rawApplicativeZero
d_rawApplicativeZero_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_206 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicativeZero_120
d_rawApplicativeZero_276 ~v0 ~v1 ~v2 v3
  = du_rawApplicativeZero_276 v3
du_rawApplicativeZero_276 ::
  T_RawMonadZero_206 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicativeZero_120
du_rawApplicativeZero_276 v0
  = coe
      MAlonzo.Code.Effect.Applicative.C_RawApplicativeZero'46'constructor_8049
      (coe d_rawApplicative_32 (coe d_rawMonad_214 (coe v0)))
      (coe d_rawEmpty_216 (coe v0))
-- Effect.Monad.RawMonadPlus
d_RawMonadPlus_284 a0 a1 a2 = ()
data T_RawMonadPlus_284
  = C_RawMonadPlus'46'constructor_9035 T_RawMonadZero_206
                                       MAlonzo.Code.Effect.Choice.T_RawChoice_16
-- Effect.Monad.RawMonadPlus.rawMonadZero
d_rawMonadZero_292 :: T_RawMonadPlus_284 -> T_RawMonadZero_206
d_rawMonadZero_292 v0
  = case coe v0 of
      C_RawMonadPlus'46'constructor_9035 v1 v2 -> coe v1
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonadPlus.rawChoice
d_rawChoice_294 ::
  T_RawMonadPlus_284 -> MAlonzo.Code.Effect.Choice.T_RawChoice_16
d_rawChoice_294 v0
  = case coe v0 of
      C_RawMonadPlus'46'constructor_9035 v1 v2 -> coe v2
      _                                        -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonadPlus._._*>_
d__'42''62'__298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__298 ~v0 ~v1 ~v2 v3 = du__'42''62'__298 v3
du__'42''62'__298 ::
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__298 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (let v2 = d_rawMonad_214 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Applicative.du__'42''62'__52
              (coe d_rawApplicative_32 (coe v2)) v5 v6))
-- Effect.Monad.RawMonadPlus._._<$_
d__'60''36'__300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__300 ~v0 ~v1 ~v2 v3 = du__'60''36'__300 v3
du__'60''36'__300 ::
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__300 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (let v2 = d_rawMonad_214 (coe v1) in
       coe
         (let v3 = d_rawApplicative_32 (coe v2) in
          coe
            (\ v4 v5 v6 v7 ->
               coe
                 MAlonzo.Code.Effect.Functor.du__'60''36'__32
                 (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v3)) v6
                 v7)))
-- Effect.Monad.RawMonadPlus._._<$>_
d__'60''36''62'__302 ::
  T_RawMonadPlus_284 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__302 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe
         MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
         (coe
            d_rawApplicative_32
            (coe d_rawMonad_214 (coe d_rawMonadZero_292 (coe v0)))))
-- Effect.Monad.RawMonadPlus._._<&>_
d__'60''38''62'__304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__304 ~v0 ~v1 ~v2 v3 = du__'60''38''62'__304 v3
du__'60''38''62'__304 ::
  T_RawMonadPlus_284 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__304 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (let v2 = d_rawMonad_214 (coe v1) in
       coe
         (let v3 = d_rawApplicative_32 (coe v2) in
          coe
            (\ v4 v5 v6 v7 ->
               coe
                 MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
                 (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v3)) v6
                 v7)))
-- Effect.Monad.RawMonadPlus._._<*_
d__'60''42'__306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__306 ~v0 ~v1 ~v2 v3 = du__'60''42'__306 v3
du__'60''42'__306 ::
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__306 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (let v2 = d_rawMonad_214 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Applicative.du__'60''42'__46
              (coe d_rawApplicative_32 (coe v2)) v5 v6))
-- Effect.Monad.RawMonadPlus._._<*>_
d__'60''42''62'__308 ::
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__308 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d__'60''42''62'__34
      (coe
         d_rawApplicative_32
         (coe d_rawMonad_214 (coe d_rawMonadZero_292 (coe v0))))
-- Effect.Monad.RawMonadPlus._._<=<_
d__'60''61''60'__310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''61''60'__310 ~v0 ~v1 ~v2 v3 = du__'60''61''60'__310 v3
du__'60''61''60'__310 ::
  T_RawMonadPlus_284 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''61''60'__310 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (\ v2 v3 v4 v5 v6 ->
         coe du__'60''61''60'__88 (coe d_rawMonad_214 (coe v1)) v5 v6)
-- Effect.Monad.RawMonadPlus._._<⊛_
d__'60''8859'__312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__312 ~v0 ~v1 ~v2 v3 = du__'60''8859'__312 v3
du__'60''8859'__312 ::
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__312 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (let v2 = d_rawMonad_214 (coe v1) in
       coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Effect.Applicative.du__'60''8859'__72
              (coe d_rawApplicative_32 (coe v2))))
-- Effect.Monad.RawMonadPlus._._=<<_
d__'61''60''60'__314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'61''60''60'__314 ~v0 ~v1 ~v2 v3 = du__'61''60''60'__314 v3
du__'61''60''60'__314 ::
  T_RawMonadPlus_284 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'61''60''60'__314 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe du__'61''60''60'__72 (coe d_rawMonad_214 (coe v1)) v4 v5)
-- Effect.Monad.RawMonadPlus._._>=>_
d__'62''61''62'__316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'62''61''62'__316 ~v0 ~v1 ~v2 v3 = du__'62''61''62'__316 v3
du__'62''61''62'__316 ::
  T_RawMonadPlus_284 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'62''61''62'__316 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (\ v2 v3 v4 v5 v6 v7 ->
         coe du__'62''61''62'__80 (coe d_rawMonad_214 (coe v1)) v5 v6 v7)
-- Effect.Monad.RawMonadPlus._._>>_
d__'62''62'__318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__318 ~v0 ~v1 ~v2 v3 = du__'62''62'__318 v3
du__'62''62'__318 ::
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__318 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe (\ v2 v3 -> coe du__'62''62'__70 (coe d_rawMonad_214 (coe v1)))
-- Effect.Monad.RawMonadPlus._._>>=_
d__'62''62''61'__320 ::
  T_RawMonadPlus_284 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__320 v0
  = coe
      d__'62''62''61'__34
      (coe d_rawMonad_214 (coe d_rawMonadZero_292 (coe v0)))
-- Effect.Monad.RawMonadPlus._._⊗_
d__'8855'__322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__322 ~v0 ~v1 ~v2 v3 = du__'8855'__322 v3
du__'8855'__322 ::
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__322 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (let v2 = d_rawMonad_214 (coe v1) in
       coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Effect.Applicative.du__'8855'__76
              (coe d_rawApplicative_32 (coe v2))))
-- Effect.Monad.RawMonadPlus._._⊛_
d__'8859'__324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__324 ~v0 ~v1 ~v2 v3 = du__'8859'__324 v3
du__'8859'__324 ::
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__324 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (let v2 = d_rawMonad_214 (coe v1) in
       coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Effect.Applicative.du__'8859'__70
              (coe d_rawApplicative_32 (coe v2))))
-- Effect.Monad.RawMonadPlus._._⊛>_
d__'8859''62'__326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__326 ~v0 ~v1 ~v2 v3 = du__'8859''62'__326 v3
du__'8859''62'__326 ::
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__326 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (let v2 = d_rawMonad_214 (coe v1) in
       coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Effect.Applicative.du__'8859''62'__74
              (coe d_rawApplicative_32 (coe v2))))
-- Effect.Monad.RawMonadPlus._.Kleisli
d_Kleisli_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadPlus_284 -> () -> () -> ()
d_Kleisli_328 = erased
-- Effect.Monad.RawMonadPlus._.empty
d_empty_330 :: T_RawMonadPlus_284 -> () -> AgdaAny
d_empty_330 v0
  = coe
      MAlonzo.Code.Effect.Empty.d_empty_22
      (coe d_rawEmpty_216 (coe d_rawMonadZero_292 (coe v0)))
-- Effect.Monad.RawMonadPlus._.ignore
d_ignore_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadPlus_284 -> () -> AgdaAny -> AgdaAny
d_ignore_332 ~v0 ~v1 ~v2 v3 = du_ignore_332 v3
du_ignore_332 :: T_RawMonadPlus_284 -> () -> AgdaAny -> AgdaAny
du_ignore_332 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (let v2 = d_rawMonad_214 (coe v1) in
       coe
         (let v3 = d_rawApplicative_32 (coe v2) in
          coe
            (\ v4 ->
               coe
                 MAlonzo.Code.Effect.Functor.du_ignore_40
                 (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v3)))))
-- Effect.Monad.RawMonadPlus._.pure
d_pure_334 :: T_RawMonadPlus_284 -> () -> AgdaAny -> AgdaAny
d_pure_334 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_pure_32
      (coe
         d_rawApplicative_32
         (coe d_rawMonad_214 (coe d_rawMonadZero_292 (coe v0))))
-- Effect.Monad.RawMonadPlus._.rawApplicative
d_rawApplicative_336 ::
  T_RawMonadPlus_284 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_rawApplicative_336 v0
  = coe
      d_rawApplicative_32
      (coe d_rawMonad_214 (coe d_rawMonadZero_292 (coe v0)))
-- Effect.Monad.RawMonadPlus._.rawApplicativeZero
d_rawApplicativeZero_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicativeZero_120
d_rawApplicativeZero_338 ~v0 ~v1 ~v2 v3
  = du_rawApplicativeZero_338 v3
du_rawApplicativeZero_338 ::
  T_RawMonadPlus_284 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicativeZero_120
du_rawApplicativeZero_338 v0
  = coe du_rawApplicativeZero_276 (coe d_rawMonadZero_292 (coe v0))
-- Effect.Monad.RawMonadPlus._.rawEmpty
d_rawEmpty_340 ::
  T_RawMonadPlus_284 -> MAlonzo.Code.Effect.Empty.T_RawEmpty_16
d_rawEmpty_340 v0
  = coe d_rawEmpty_216 (coe d_rawMonadZero_292 (coe v0))
-- Effect.Monad.RawMonadPlus._.rawFunctor
d_rawFunctor_342 ::
  T_RawMonadPlus_284 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_342 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
      (coe
         d_rawApplicative_32
         (coe d_rawMonad_214 (coe d_rawMonadZero_292 (coe v0))))
-- Effect.Monad.RawMonadPlus._.rawMonad
d_rawMonad_344 :: T_RawMonadPlus_284 -> T_RawMonad_24
d_rawMonad_344 v0
  = coe d_rawMonad_214 (coe d_rawMonadZero_292 (coe v0))
-- Effect.Monad.RawMonadPlus._.return
d_return_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadPlus_284 -> () -> AgdaAny -> AgdaAny
d_return_346 ~v0 ~v1 ~v2 v3 = du_return_346 v3
du_return_346 :: T_RawMonadPlus_284 -> () -> AgdaAny -> AgdaAny
du_return_346 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (let v2 = d_rawMonad_214 (coe v1) in
       coe
         (\ v3 ->
            coe
              MAlonzo.Code.Effect.Applicative.du_return_68
              (coe d_rawApplicative_32 (coe v2))))
-- Effect.Monad.RawMonadPlus._.unless
d_unless_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadPlus_284 -> Bool -> AgdaAny -> AgdaAny
d_unless_348 ~v0 ~v1 ~v2 v3 = du_unless_348 v3
du_unless_348 :: T_RawMonadPlus_284 -> Bool -> AgdaAny -> AgdaAny
du_unless_348 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe (coe du_unless_96 (coe d_rawMonad_214 (coe v1)))
-- Effect.Monad.RawMonadPlus._.when
d_when_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadPlus_284 -> Bool -> AgdaAny -> AgdaAny
d_when_350 ~v0 ~v1 ~v2 v3 = du_when_350 v3
du_when_350 :: T_RawMonadPlus_284 -> Bool -> AgdaAny -> AgdaAny
du_when_350 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe (coe du_when_90 (coe d_rawMonad_214 (coe v1)))
-- Effect.Monad.RawMonadPlus._.zip
d_zip_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_352 ~v0 ~v1 ~v2 v3 = du_zip_352 v3
du_zip_352 ::
  T_RawMonadPlus_284 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_352 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (let v2 = d_rawMonad_214 (coe v1) in
       coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Effect.Applicative.du_zip_66
              (coe d_rawApplicative_32 (coe v2))))
-- Effect.Monad.RawMonadPlus._.zipWith
d_zipWith_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_354 ~v0 ~v1 ~v2 v3 = du_zipWith_354 v3
du_zipWith_354 ::
  T_RawMonadPlus_284 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_354 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (let v2 = d_rawMonad_214 (coe v1) in
       coe
         (\ v3 v4 v5 v6 v7 v8 ->
            coe
              MAlonzo.Code.Effect.Applicative.du_zipWith_58
              (coe d_rawApplicative_32 (coe v2)) v6 v7 v8))
-- Effect.Monad.RawMonadPlus._.∅
d_'8709'_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadPlus_284 -> () -> AgdaAny
d_'8709'_356 ~v0 ~v1 ~v2 v3 = du_'8709'_356 v3
du_'8709'_356 :: T_RawMonadPlus_284 -> () -> AgdaAny
du_'8709'_356 v0
  = let v1 = d_rawMonadZero_292 (coe v0) in
    coe
      (\ v2 ->
         coe
           MAlonzo.Code.Effect.Empty.du_'8709'_24
           (coe d_rawEmpty_216 (coe v1)))
-- Effect.Monad.RawMonadPlus._._<|>_
d__'60''124''62'__360 ::
  T_RawMonadPlus_284 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''124''62'__360 v0
  = coe
      MAlonzo.Code.Effect.Choice.d__'60''124''62'__22
      (coe d_rawChoice_294 (coe v0))
-- Effect.Monad.RawMonadPlus._._∣_
d__'8739'__362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8739'__362 ~v0 ~v1 ~v2 v3 = du__'8739'__362 v3
du__'8739'__362 ::
  T_RawMonadPlus_284 -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8739'__362 v0 v1
  = coe
      MAlonzo.Code.Effect.Choice.du__'8739'__24
      (coe d_rawChoice_294 (coe v0))
-- Effect.Monad.RawMonadPlus.rawAlternative
d_rawAlternative_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_284 ->
  MAlonzo.Code.Effect.Applicative.T_RawAlternative_180
d_rawAlternative_364 ~v0 ~v1 ~v2 v3 = du_rawAlternative_364 v3
du_rawAlternative_364 ::
  T_RawMonadPlus_284 ->
  MAlonzo.Code.Effect.Applicative.T_RawAlternative_180
du_rawAlternative_364 v0
  = coe
      MAlonzo.Code.Effect.Applicative.C_RawAlternative'46'constructor_9897
      (coe du_rawApplicativeZero_276 (coe d_rawMonadZero_292 (coe v0)))
      (coe d_rawChoice_294 (coe v0))
-- Effect.Monad.RawMonadTd
d_RawMonadTd_376 a0 a1 a2 a3 a4 = ()
data T_RawMonadTd_376
  = C_RawMonadTd'46'constructor_11233 (() -> AgdaAny -> AgdaAny)
                                      T_RawMonad_24
-- Effect.Monad.RawMonadTd.lift
d_lift_386 :: T_RawMonadTd_376 -> () -> AgdaAny -> AgdaAny
d_lift_386 v0
  = case coe v0 of
      C_RawMonadTd'46'constructor_11233 v1 v2 -> coe v1
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonadTd.rawMonad
d_rawMonad_388 :: T_RawMonadTd_376 -> T_RawMonad_24
d_rawMonad_388 v0
  = case coe v0 of
      C_RawMonadTd'46'constructor_11233 v1 v2 -> coe v2
      _                                       -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonadTd._._*>_
d__'42''62'__392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__392 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'42''62'__392 v5
du__'42''62'__392 ::
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__392 v0
  = let v1 = d_rawMonad_388 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'42''62'__52
           (coe d_rawApplicative_32 (coe v1)) v4 v5)
-- Effect.Monad.RawMonadTd._._<$_
d__'60''36'__394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__394 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'60''36'__394 v5
du__'60''36'__394 ::
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__394 v0
  = let v1 = d_rawMonad_388 (coe v0) in
    coe
      (let v2 = d_rawApplicative_32 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Functor.du__'60''36'__32
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v2)) v5
              v6))
-- Effect.Monad.RawMonadTd._._<$>_
d__'60''36''62'__396 ::
  T_RawMonadTd_376 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__396 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe
         MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
         (coe d_rawApplicative_32 (coe d_rawMonad_388 (coe v0))))
-- Effect.Monad.RawMonadTd._._<&>_
d__'60''38''62'__398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_376 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__398 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du__'60''38''62'__398 v5
du__'60''38''62'__398 ::
  T_RawMonadTd_376 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__398 v0
  = let v1 = d_rawMonad_388 (coe v0) in
    coe
      (let v2 = d_rawApplicative_32 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v2)) v5
              v6))
-- Effect.Monad.RawMonadTd._._<*_
d__'60''42'__400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__400 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'60''42'__400 v5
du__'60''42'__400 ::
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__400 v0
  = let v1 = d_rawMonad_388 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'60''42'__46
           (coe d_rawApplicative_32 (coe v1)) v4 v5)
-- Effect.Monad.RawMonadTd._._<*>_
d__'60''42''62'__402 ::
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__402 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d__'60''42''62'__34
      (coe d_rawApplicative_32 (coe d_rawMonad_388 (coe v0)))
-- Effect.Monad.RawMonadTd._._<=<_
d__'60''61''60'__404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_376 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''61''60'__404 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du__'60''61''60'__404 v5
du__'60''61''60'__404 ::
  T_RawMonadTd_376 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''61''60'__404 v0 v1 v2 v3 v4 v5
  = coe du__'60''61''60'__88 (coe d_rawMonad_388 (coe v0)) v4 v5
-- Effect.Monad.RawMonadTd._._<⊛_
d__'60''8859'__406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__406 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'60''8859'__406 v5
du__'60''8859'__406 ::
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__406 v0
  = let v1 = d_rawMonad_388 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'60''8859'__72
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadTd._._=<<_
d__'61''60''60'__408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_376 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'61''60''60'__408 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du__'61''60''60'__408 v5
du__'61''60''60'__408 ::
  T_RawMonadTd_376 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'61''60''60'__408 v0 v1 v2 v3 v4
  = coe du__'61''60''60'__72 (coe d_rawMonad_388 (coe v0)) v3 v4
-- Effect.Monad.RawMonadTd._._>=>_
d__'62''61''62'__410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_376 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'62''61''62'__410 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du__'62''61''62'__410 v5
du__'62''61''62'__410 ::
  T_RawMonadTd_376 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'62''61''62'__410 v0 v1 v2 v3 v4 v5 v6
  = coe du__'62''61''62'__80 (coe d_rawMonad_388 (coe v0)) v4 v5 v6
-- Effect.Monad.RawMonadTd._._>>_
d__'62''62'__412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__412 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'62''62'__412 v5
du__'62''62'__412 ::
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__412 v0 v1 v2
  = coe du__'62''62'__70 (coe d_rawMonad_388 (coe v0))
-- Effect.Monad.RawMonadTd._._>>=_
d__'62''62''61'__414 ::
  T_RawMonadTd_376 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__414 v0
  = coe d__'62''62''61'__34 (coe d_rawMonad_388 (coe v0))
-- Effect.Monad.RawMonadTd._._⊗_
d__'8855'__416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__416 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'8855'__416 v5
du__'8855'__416 ::
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__416 v0
  = let v1 = d_rawMonad_388 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8855'__76
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadTd._._⊛_
d__'8859'__418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__418 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'8859'__418 v5
du__'8859'__418 ::
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__418 v0
  = let v1 = d_rawMonad_388 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8859'__70
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadTd._._⊛>_
d__'8859''62'__420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__420 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'8859''62'__420 v5
du__'8859''62'__420 ::
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__420 v0
  = let v1 = d_rawMonad_388 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8859''62'__74
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadTd._.Kleisli
d_Kleisli_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> (() -> ()) -> T_RawMonadTd_376 -> () -> () -> ()
d_Kleisli_422 = erased
-- Effect.Monad.RawMonadTd._.ignore
d_ignore_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) -> T_RawMonadTd_376 -> () -> AgdaAny -> AgdaAny
d_ignore_424 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_ignore_424 v5
du_ignore_424 :: T_RawMonadTd_376 -> () -> AgdaAny -> AgdaAny
du_ignore_424 v0
  = let v1 = d_rawMonad_388 (coe v0) in
    coe
      (let v2 = d_rawApplicative_32 (coe v1) in
       coe
         (\ v3 ->
            coe
              MAlonzo.Code.Effect.Functor.du_ignore_40
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v2))))
-- Effect.Monad.RawMonadTd._.pure
d_pure_426 :: T_RawMonadTd_376 -> () -> AgdaAny -> AgdaAny
d_pure_426 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_pure_32
      (coe d_rawApplicative_32 (coe d_rawMonad_388 (coe v0)))
-- Effect.Monad.RawMonadTd._.rawApplicative
d_rawApplicative_428 ::
  T_RawMonadTd_376 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_rawApplicative_428 v0
  = coe d_rawApplicative_32 (coe d_rawMonad_388 (coe v0))
-- Effect.Monad.RawMonadTd._.rawFunctor
d_rawFunctor_430 ::
  T_RawMonadTd_376 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_430 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
      (coe d_rawApplicative_32 (coe d_rawMonad_388 (coe v0)))
-- Effect.Monad.RawMonadTd._.return
d_return_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) -> T_RawMonadTd_376 -> () -> AgdaAny -> AgdaAny
d_return_432 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_return_432 v5
du_return_432 :: T_RawMonadTd_376 -> () -> AgdaAny -> AgdaAny
du_return_432 v0
  = let v1 = d_rawMonad_388 (coe v0) in
    coe
      (\ v2 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_return_68
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadTd._.unless
d_unless_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) -> T_RawMonadTd_376 -> Bool -> AgdaAny -> AgdaAny
d_unless_434 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_unless_434 v5
du_unless_434 :: T_RawMonadTd_376 -> Bool -> AgdaAny -> AgdaAny
du_unless_434 v0 = coe du_unless_96 (coe d_rawMonad_388 (coe v0))
-- Effect.Monad.RawMonadTd._.when
d_when_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) -> T_RawMonadTd_376 -> Bool -> AgdaAny -> AgdaAny
d_when_436 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_when_436 v5
du_when_436 :: T_RawMonadTd_376 -> Bool -> AgdaAny -> AgdaAny
du_when_436 v0 = coe du_when_90 (coe d_rawMonad_388 (coe v0))
-- Effect.Monad.RawMonadTd._.zip
d_zip_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_438 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_zip_438 v5
du_zip_438 ::
  T_RawMonadTd_376 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_438 v0
  = let v1 = d_rawMonad_388 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_zip_66
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadTd._.zipWith
d_zipWith_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_376 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_440 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_zipWith_440 v5
du_zipWith_440 ::
  T_RawMonadTd_376 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_440 v0
  = let v1 = d_rawMonad_388 (coe v0) in
    coe
      (\ v2 v3 v4 v5 v6 v7 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_zipWith_58
           (coe d_rawApplicative_32 (coe v1)) v5 v6 v7)
-- Effect.Monad.RawMonadT
d_RawMonadT_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((() -> ()) -> () -> ()) -> ()
d_RawMonadT_444 = erased
