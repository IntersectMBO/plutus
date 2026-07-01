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

module MAlonzo.Code.Effect.Monad where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Effect.Applicative
import qualified MAlonzo.Code.Effect.Choice
import qualified MAlonzo.Code.Effect.Empty
import qualified MAlonzo.Code.Effect.Functor
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Level

-- Effect.Monad.RawMonad
d_RawMonad_24 a0 a1 a2 = ()
data T_RawMonad_24
  = C_constructor_98 MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
                     (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
-- Effect.Monad.RawMonad.rawApplicative
d_rawApplicative_32 ::
  T_RawMonad_24 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_rawApplicative_32 v0
  = case coe v0 of
      C_constructor_98 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonad._>>=_
d__'62''62''61'__34 ::
  T_RawMonad_24 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__34 v0
  = case coe v0 of
      C_constructor_98 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
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
d__'42''62'__110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__110 ~v0 ~v1 v2 = du__'42''62'__110 v2
du__'42''62'__110 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__110 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Applicative.du__'42''62'__52
      (coe d_rawApplicative_32 (coe v0)) v3 v4
-- Effect.Monad.Join._._<$_
d__'60''36'__112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__112 ~v0 ~v1 v2 = du__'60''36'__112 v2
du__'60''36'__112 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__112 v0
  = let v1 = d_rawApplicative_32 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Functor.du__'60''36'__32
           (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v1)) v4
           v5)
-- Effect.Monad.Join._._<$>_
d__'60''36''62'__114 ::
  T_RawMonad_24 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__114 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe
         MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
         (coe d_rawApplicative_32 (coe v0)))
-- Effect.Monad.Join._._<&>_
d__'60''38''62'__116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__116 ~v0 ~v1 v2 = du__'60''38''62'__116 v2
du__'60''38''62'__116 ::
  T_RawMonad_24 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__116 v0
  = let v1 = d_rawApplicative_32 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
           (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v1)) v4
           v5)
-- Effect.Monad.Join._._<*_
d__'60''42'__118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__118 ~v0 ~v1 v2 = du__'60''42'__118 v2
du__'60''42'__118 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__118 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Applicative.du__'60''42'__46
      (coe d_rawApplicative_32 (coe v0)) v3 v4
-- Effect.Monad.Join._._<*>_
d__'60''42''62'__120 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__120 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d__'60''42''62'__34
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._._<=<_
d__'60''61''60'__122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''61''60'__122 ~v0 ~v1 v2 = du__'60''61''60'__122 v2
du__'60''61''60'__122 ::
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''61''60'__122 v0 v1 v2 v3 v4 v5
  = coe du__'60''61''60'__88 (coe v0) v4 v5
-- Effect.Monad.Join._._<⊛_
d__'60''8859'__124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__124 ~v0 ~v1 v2 = du__'60''8859'__124 v2
du__'60''8859'__124 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__124 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du__'60''8859'__72
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._._=<<_
d__'61''60''60'__126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'61''60''60'__126 ~v0 ~v1 v2 = du__'61''60''60'__126 v2
du__'61''60''60'__126 ::
  T_RawMonad_24 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'61''60''60'__126 v0 v1 v2 v3 v4
  = coe du__'61''60''60'__72 (coe v0) v3 v4
-- Effect.Monad.Join._._>=>_
d__'62''61''62'__128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'62''61''62'__128 ~v0 ~v1 v2 = du__'62''61''62'__128 v2
du__'62''61''62'__128 ::
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'62''61''62'__128 v0 v1 v2 v3 v4 v5 v6
  = coe du__'62''61''62'__80 (coe v0) v4 v5 v6
-- Effect.Monad.Join._._>>_
d__'62''62'__130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__130 ~v0 ~v1 v2 = du__'62''62'__130 v2
du__'62''62'__130 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__130 v0 v1 v2 = coe du__'62''62'__70 (coe v0)
-- Effect.Monad.Join._._>>=_
d__'62''62''61'__132 ::
  T_RawMonad_24 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__132 v0 = coe d__'62''62''61'__34 (coe v0)
-- Effect.Monad.Join._._⊗_
d__'8855'__134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__134 ~v0 ~v1 v2 = du__'8855'__134 v2
du__'8855'__134 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__134 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du__'8855'__76
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._._⊛_
d__'8859'__136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__136 ~v0 ~v1 v2 = du__'8859'__136 v2
du__'8859'__136 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__136 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du__'8859'__70
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._._⊛>_
d__'8859''62'__138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__138 ~v0 ~v1 v2 = du__'8859''62'__138 v2
du__'8859''62'__138 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__138 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du__'8859''62'__74
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._.Kleisli
d_Kleisli_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> () -> () -> ()
d_Kleisli_140 = erased
-- Effect.Monad.Join._.ignore
d_ignore_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
d_ignore_142 ~v0 ~v1 v2 = du_ignore_142 v2
du_ignore_142 :: T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
du_ignore_142 v0
  = let v1 = d_rawApplicative_32 (coe v0) in
    coe
      (\ v2 ->
         coe
           MAlonzo.Code.Effect.Functor.du_ignore_40
           (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v1)))
-- Effect.Monad.Join._.pure
d_pure_144 :: T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
d_pure_144 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_pure_32
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._.rawApplicative
d_rawApplicative_146 ::
  T_RawMonad_24 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_rawApplicative_146 v0 = coe d_rawApplicative_32 (coe v0)
-- Effect.Monad.Join._.rawFunctor
d_rawFunctor_148 ::
  T_RawMonad_24 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_148 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._.return
d_return_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
d_return_150 ~v0 ~v1 v2 = du_return_150 v2
du_return_150 :: T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
du_return_150 v0 v1
  = coe
      MAlonzo.Code.Effect.Applicative.du_return_68
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._.unless
d_unless_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> Bool -> AgdaAny -> AgdaAny
d_unless_152 ~v0 ~v1 v2 = du_unless_152 v2
du_unless_152 :: T_RawMonad_24 -> Bool -> AgdaAny -> AgdaAny
du_unless_152 v0 = coe du_unless_96 (coe v0)
-- Effect.Monad.Join._.when
d_when_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> Bool -> AgdaAny -> AgdaAny
d_when_154 ~v0 ~v1 v2 = du_when_154 v2
du_when_154 :: T_RawMonad_24 -> Bool -> AgdaAny -> AgdaAny
du_when_154 v0 = coe du_when_90 (coe v0)
-- Effect.Monad.Join._.zip
d_zip_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_156 ~v0 ~v1 v2 = du_zip_156 v2
du_zip_156 ::
  T_RawMonad_24 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_156 v0 v1 v2
  = coe
      MAlonzo.Code.Effect.Applicative.du_zip_66
      (coe d_rawApplicative_32 (coe v0))
-- Effect.Monad.Join._.zipWith
d_zipWith_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_158 ~v0 ~v1 v2 = du_zipWith_158 v2
du_zipWith_158 ::
  T_RawMonad_24 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_158 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Effect.Applicative.du_zipWith_58
      (coe d_rawApplicative_32 (coe v0)) v4 v5 v6
-- Effect.Monad.Join.join
d_join_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonad_24 -> () -> AgdaAny -> AgdaAny
d_join_160 ~v0 ~v1 v2 ~v3 v4 = du_join_160 v2 v4
du_join_160 :: T_RawMonad_24 -> AgdaAny -> AgdaAny
du_join_160 v0 v1
  = coe d__'62''62''61'__34 v0 erased erased v1 (\ v2 -> v2)
-- Effect.Monad._.mkRawMonad
d_mkRawMonad_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> AgdaAny -> AgdaAny) ->
  (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  T_RawMonad_24
d_mkRawMonad_180 ~v0 ~v1 ~v2 v3 v4 = du_mkRawMonad_180 v3 v4
du_mkRawMonad_180 ::
  (() -> AgdaAny -> AgdaAny) ->
  (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny) ->
  T_RawMonad_24
du_mkRawMonad_180 v0 v1
  = coe
      C_constructor_98
      (let v2
             = coe
                 MAlonzo.Code.Effect.Applicative.du_mkRawApplicative_96 (coe v0) in
       coe
         (coe
            v2
            (\ v3 v4 v5 v6 ->
               coe
                 v1 () v4 v5
                 (\ v7 -> coe v1 v3 v4 v6 (\ v8 -> coe v0 v4 (coe v7 v8))))))
      (coe (\ v2 v3 -> coe v1 v2 v3))
-- Effect.Monad.RawMonadZero
d_RawMonadZero_208 a0 a1 a2 = ()
data T_RawMonadZero_208
  = C_constructor_280 T_RawMonad_24
                      MAlonzo.Code.Effect.Empty.T_RawEmpty_16
-- Effect.Monad.RawMonadZero.rawMonad
d_rawMonad_216 :: T_RawMonadZero_208 -> T_RawMonad_24
d_rawMonad_216 v0
  = case coe v0 of
      C_constructor_280 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonadZero.rawEmpty
d_rawEmpty_218 ::
  T_RawMonadZero_208 -> MAlonzo.Code.Effect.Empty.T_RawEmpty_16
d_rawEmpty_218 v0
  = case coe v0 of
      C_constructor_280 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonadZero._._*>_
d__'42''62'__222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__222 ~v0 ~v1 ~v2 v3 = du__'42''62'__222 v3
du__'42''62'__222 ::
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__222 v0
  = let v1 = d_rawMonad_216 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'42''62'__52
           (coe d_rawApplicative_32 (coe v1)) v4 v5)
-- Effect.Monad.RawMonadZero._._<$_
d__'60''36'__224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__224 ~v0 ~v1 ~v2 v3 = du__'60''36'__224 v3
du__'60''36'__224 ::
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__224 v0
  = let v1 = d_rawMonad_216 (coe v0) in
    coe
      (let v2 = d_rawApplicative_32 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Functor.du__'60''36'__32
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v2)) v5
              v6))
-- Effect.Monad.RawMonadZero._._<$>_
d__'60''36''62'__226 ::
  T_RawMonadZero_208 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__226 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe
         MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
         (coe d_rawApplicative_32 (coe d_rawMonad_216 (coe v0))))
-- Effect.Monad.RawMonadZero._._<&>_
d__'60''38''62'__228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__228 ~v0 ~v1 ~v2 v3 = du__'60''38''62'__228 v3
du__'60''38''62'__228 ::
  T_RawMonadZero_208 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__228 v0
  = let v1 = d_rawMonad_216 (coe v0) in
    coe
      (let v2 = d_rawApplicative_32 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v2)) v5
              v6))
-- Effect.Monad.RawMonadZero._._<*_
d__'60''42'__230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__230 ~v0 ~v1 ~v2 v3 = du__'60''42'__230 v3
du__'60''42'__230 ::
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__230 v0
  = let v1 = d_rawMonad_216 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'60''42'__46
           (coe d_rawApplicative_32 (coe v1)) v4 v5)
-- Effect.Monad.RawMonadZero._._<*>_
d__'60''42''62'__232 ::
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__232 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d__'60''42''62'__34
      (coe d_rawApplicative_32 (coe d_rawMonad_216 (coe v0)))
-- Effect.Monad.RawMonadZero._._<=<_
d__'60''61''60'__234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''61''60'__234 ~v0 ~v1 ~v2 v3 = du__'60''61''60'__234 v3
du__'60''61''60'__234 ::
  T_RawMonadZero_208 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''61''60'__234 v0 v1 v2 v3 v4 v5
  = coe du__'60''61''60'__88 (coe d_rawMonad_216 (coe v0)) v4 v5
-- Effect.Monad.RawMonadZero._._<⊛_
d__'60''8859'__236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__236 ~v0 ~v1 ~v2 v3 = du__'60''8859'__236 v3
du__'60''8859'__236 ::
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__236 v0
  = let v1 = d_rawMonad_216 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'60''8859'__72
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadZero._._=<<_
d__'61''60''60'__238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'61''60''60'__238 ~v0 ~v1 ~v2 v3 = du__'61''60''60'__238 v3
du__'61''60''60'__238 ::
  T_RawMonadZero_208 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'61''60''60'__238 v0 v1 v2 v3 v4
  = coe du__'61''60''60'__72 (coe d_rawMonad_216 (coe v0)) v3 v4
-- Effect.Monad.RawMonadZero._._>=>_
d__'62''61''62'__240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'62''61''62'__240 ~v0 ~v1 ~v2 v3 = du__'62''61''62'__240 v3
du__'62''61''62'__240 ::
  T_RawMonadZero_208 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'62''61''62'__240 v0 v1 v2 v3 v4 v5 v6
  = coe du__'62''61''62'__80 (coe d_rawMonad_216 (coe v0)) v4 v5 v6
-- Effect.Monad.RawMonadZero._._>>_
d__'62''62'__242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__242 ~v0 ~v1 ~v2 v3 = du__'62''62'__242 v3
du__'62''62'__242 ::
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__242 v0 v1 v2
  = coe du__'62''62'__70 (coe d_rawMonad_216 (coe v0))
-- Effect.Monad.RawMonadZero._._>>=_
d__'62''62''61'__244 ::
  T_RawMonadZero_208 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__244 v0
  = coe d__'62''62''61'__34 (coe d_rawMonad_216 (coe v0))
-- Effect.Monad.RawMonadZero._._⊗_
d__'8855'__246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__246 ~v0 ~v1 ~v2 v3 = du__'8855'__246 v3
du__'8855'__246 ::
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__246 v0
  = let v1 = d_rawMonad_216 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8855'__76
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadZero._._⊛_
d__'8859'__248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__248 ~v0 ~v1 ~v2 v3 = du__'8859'__248 v3
du__'8859'__248 ::
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__248 v0
  = let v1 = d_rawMonad_216 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8859'__70
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadZero._._⊛>_
d__'8859''62'__250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__250 ~v0 ~v1 ~v2 v3 = du__'8859''62'__250 v3
du__'8859''62'__250 ::
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__250 v0
  = let v1 = d_rawMonad_216 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8859''62'__74
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadZero._.Kleisli
d_Kleisli_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadZero_208 -> () -> () -> ()
d_Kleisli_252 = erased
-- Effect.Monad.RawMonadZero._.ignore
d_ignore_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadZero_208 -> () -> AgdaAny -> AgdaAny
d_ignore_254 ~v0 ~v1 ~v2 v3 = du_ignore_254 v3
du_ignore_254 :: T_RawMonadZero_208 -> () -> AgdaAny -> AgdaAny
du_ignore_254 v0
  = let v1 = d_rawMonad_216 (coe v0) in
    coe
      (let v2 = d_rawApplicative_32 (coe v1) in
       coe
         (\ v3 ->
            coe
              MAlonzo.Code.Effect.Functor.du_ignore_40
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v2))))
-- Effect.Monad.RawMonadZero._.pure
d_pure_256 :: T_RawMonadZero_208 -> () -> AgdaAny -> AgdaAny
d_pure_256 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_pure_32
      (coe d_rawApplicative_32 (coe d_rawMonad_216 (coe v0)))
-- Effect.Monad.RawMonadZero._.rawApplicative
d_rawApplicative_258 ::
  T_RawMonadZero_208 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_rawApplicative_258 v0
  = coe d_rawApplicative_32 (coe d_rawMonad_216 (coe v0))
-- Effect.Monad.RawMonadZero._.rawFunctor
d_rawFunctor_260 ::
  T_RawMonadZero_208 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_260 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
      (coe d_rawApplicative_32 (coe d_rawMonad_216 (coe v0)))
-- Effect.Monad.RawMonadZero._.return
d_return_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadZero_208 -> () -> AgdaAny -> AgdaAny
d_return_262 ~v0 ~v1 ~v2 v3 = du_return_262 v3
du_return_262 :: T_RawMonadZero_208 -> () -> AgdaAny -> AgdaAny
du_return_262 v0
  = let v1 = d_rawMonad_216 (coe v0) in
    coe
      (\ v2 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_return_68
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadZero._.unless
d_unless_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadZero_208 -> Bool -> AgdaAny -> AgdaAny
d_unless_264 ~v0 ~v1 ~v2 v3 = du_unless_264 v3
du_unless_264 :: T_RawMonadZero_208 -> Bool -> AgdaAny -> AgdaAny
du_unless_264 v0 = coe du_unless_96 (coe d_rawMonad_216 (coe v0))
-- Effect.Monad.RawMonadZero._.when
d_when_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadZero_208 -> Bool -> AgdaAny -> AgdaAny
d_when_266 ~v0 ~v1 ~v2 v3 = du_when_266 v3
du_when_266 :: T_RawMonadZero_208 -> Bool -> AgdaAny -> AgdaAny
du_when_266 v0 = coe du_when_90 (coe d_rawMonad_216 (coe v0))
-- Effect.Monad.RawMonadZero._.zip
d_zip_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_268 ~v0 ~v1 ~v2 v3 = du_zip_268 v3
du_zip_268 ::
  T_RawMonadZero_208 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_268 v0
  = let v1 = d_rawMonad_216 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_zip_66
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadZero._.zipWith
d_zipWith_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_270 ~v0 ~v1 ~v2 v3 = du_zipWith_270 v3
du_zipWith_270 ::
  T_RawMonadZero_208 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_270 v0
  = let v1 = d_rawMonad_216 (coe v0) in
    coe
      (\ v2 v3 v4 v5 v6 v7 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_zipWith_58
           (coe d_rawApplicative_32 (coe v1)) v5 v6 v7)
-- Effect.Monad.RawMonadZero._.empty
d_empty_274 :: T_RawMonadZero_208 -> () -> AgdaAny
d_empty_274 v0
  = coe
      MAlonzo.Code.Effect.Empty.d_empty_22 (coe d_rawEmpty_218 (coe v0))
-- Effect.Monad.RawMonadZero._.∅
d_'8709'_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadZero_208 -> () -> AgdaAny
d_'8709'_276 ~v0 ~v1 ~v2 v3 = du_'8709'_276 v3
du_'8709'_276 :: T_RawMonadZero_208 -> () -> AgdaAny
du_'8709'_276 v0 v1
  = coe
      MAlonzo.Code.Effect.Empty.du_'8709'_24
      (coe d_rawEmpty_218 (coe v0))
-- Effect.Monad.RawMonadZero.rawApplicativeZero
d_rawApplicativeZero_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadZero_208 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicativeZero_122
d_rawApplicativeZero_278 ~v0 ~v1 ~v2 v3
  = du_rawApplicativeZero_278 v3
du_rawApplicativeZero_278 ::
  T_RawMonadZero_208 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicativeZero_122
du_rawApplicativeZero_278 v0
  = coe
      MAlonzo.Code.Effect.Applicative.C_constructor_176
      (coe d_rawApplicative_32 (coe d_rawMonad_216 (coe v0)))
      (coe d_rawEmpty_218 (coe v0))
-- Effect.Monad.RawMonadPlus
d_RawMonadPlus_288 a0 a1 a2 = ()
data T_RawMonadPlus_288
  = C_constructor_370 T_RawMonadZero_208
                      MAlonzo.Code.Effect.Choice.T_RawChoice_16
-- Effect.Monad.RawMonadPlus.rawMonadZero
d_rawMonadZero_296 :: T_RawMonadPlus_288 -> T_RawMonadZero_208
d_rawMonadZero_296 v0
  = case coe v0 of
      C_constructor_370 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonadPlus.rawChoice
d_rawChoice_298 ::
  T_RawMonadPlus_288 -> MAlonzo.Code.Effect.Choice.T_RawChoice_16
d_rawChoice_298 v0
  = case coe v0 of
      C_constructor_370 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonadPlus._._*>_
d__'42''62'__302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__302 ~v0 ~v1 ~v2 v3 = du__'42''62'__302 v3
du__'42''62'__302 ::
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__302 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (let v2 = d_rawMonad_216 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Applicative.du__'42''62'__52
              (coe d_rawApplicative_32 (coe v2)) v5 v6))
-- Effect.Monad.RawMonadPlus._._<$_
d__'60''36'__304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__304 ~v0 ~v1 ~v2 v3 = du__'60''36'__304 v3
du__'60''36'__304 ::
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__304 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (let v2 = d_rawMonad_216 (coe v1) in
       coe
         (let v3 = d_rawApplicative_32 (coe v2) in
          coe
            (\ v4 v5 v6 v7 ->
               coe
                 MAlonzo.Code.Effect.Functor.du__'60''36'__32
                 (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v3)) v6
                 v7)))
-- Effect.Monad.RawMonadPlus._._<$>_
d__'60''36''62'__306 ::
  T_RawMonadPlus_288 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__306 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe
         MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
         (coe
            d_rawApplicative_32
            (coe d_rawMonad_216 (coe d_rawMonadZero_296 (coe v0)))))
-- Effect.Monad.RawMonadPlus._._<&>_
d__'60''38''62'__308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__308 ~v0 ~v1 ~v2 v3 = du__'60''38''62'__308 v3
du__'60''38''62'__308 ::
  T_RawMonadPlus_288 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__308 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (let v2 = d_rawMonad_216 (coe v1) in
       coe
         (let v3 = d_rawApplicative_32 (coe v2) in
          coe
            (\ v4 v5 v6 v7 ->
               coe
                 MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
                 (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v3)) v6
                 v7)))
-- Effect.Monad.RawMonadPlus._._<*_
d__'60''42'__310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__310 ~v0 ~v1 ~v2 v3 = du__'60''42'__310 v3
du__'60''42'__310 ::
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__310 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (let v2 = d_rawMonad_216 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Applicative.du__'60''42'__46
              (coe d_rawApplicative_32 (coe v2)) v5 v6))
-- Effect.Monad.RawMonadPlus._._<*>_
d__'60''42''62'__312 ::
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__312 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d__'60''42''62'__34
      (coe
         d_rawApplicative_32
         (coe d_rawMonad_216 (coe d_rawMonadZero_296 (coe v0))))
-- Effect.Monad.RawMonadPlus._._<=<_
d__'60''61''60'__314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''61''60'__314 ~v0 ~v1 ~v2 v3 = du__'60''61''60'__314 v3
du__'60''61''60'__314 ::
  T_RawMonadPlus_288 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''61''60'__314 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (\ v2 v3 v4 v5 v6 ->
         coe du__'60''61''60'__88 (coe d_rawMonad_216 (coe v1)) v5 v6)
-- Effect.Monad.RawMonadPlus._._<⊛_
d__'60''8859'__316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__316 ~v0 ~v1 ~v2 v3 = du__'60''8859'__316 v3
du__'60''8859'__316 ::
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__316 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (let v2 = d_rawMonad_216 (coe v1) in
       coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Effect.Applicative.du__'60''8859'__72
              (coe d_rawApplicative_32 (coe v2))))
-- Effect.Monad.RawMonadPlus._._=<<_
d__'61''60''60'__318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'61''60''60'__318 ~v0 ~v1 ~v2 v3 = du__'61''60''60'__318 v3
du__'61''60''60'__318 ::
  T_RawMonadPlus_288 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'61''60''60'__318 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe du__'61''60''60'__72 (coe d_rawMonad_216 (coe v1)) v4 v5)
-- Effect.Monad.RawMonadPlus._._>=>_
d__'62''61''62'__320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'62''61''62'__320 ~v0 ~v1 ~v2 v3 = du__'62''61''62'__320 v3
du__'62''61''62'__320 ::
  T_RawMonadPlus_288 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'62''61''62'__320 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (\ v2 v3 v4 v5 v6 v7 ->
         coe du__'62''61''62'__80 (coe d_rawMonad_216 (coe v1)) v5 v6 v7)
-- Effect.Monad.RawMonadPlus._._>>_
d__'62''62'__322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__322 ~v0 ~v1 ~v2 v3 = du__'62''62'__322 v3
du__'62''62'__322 ::
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__322 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe (\ v2 v3 -> coe du__'62''62'__70 (coe d_rawMonad_216 (coe v1)))
-- Effect.Monad.RawMonadPlus._._>>=_
d__'62''62''61'__324 ::
  T_RawMonadPlus_288 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__324 v0
  = coe
      d__'62''62''61'__34
      (coe d_rawMonad_216 (coe d_rawMonadZero_296 (coe v0)))
-- Effect.Monad.RawMonadPlus._._⊗_
d__'8855'__326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__326 ~v0 ~v1 ~v2 v3 = du__'8855'__326 v3
du__'8855'__326 ::
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__326 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (let v2 = d_rawMonad_216 (coe v1) in
       coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Effect.Applicative.du__'8855'__76
              (coe d_rawApplicative_32 (coe v2))))
-- Effect.Monad.RawMonadPlus._._⊛_
d__'8859'__328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__328 ~v0 ~v1 ~v2 v3 = du__'8859'__328 v3
du__'8859'__328 ::
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__328 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (let v2 = d_rawMonad_216 (coe v1) in
       coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Effect.Applicative.du__'8859'__70
              (coe d_rawApplicative_32 (coe v2))))
-- Effect.Monad.RawMonadPlus._._⊛>_
d__'8859''62'__330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__330 ~v0 ~v1 ~v2 v3 = du__'8859''62'__330 v3
du__'8859''62'__330 ::
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__330 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (let v2 = d_rawMonad_216 (coe v1) in
       coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Effect.Applicative.du__'8859''62'__74
              (coe d_rawApplicative_32 (coe v2))))
-- Effect.Monad.RawMonadPlus._.Kleisli
d_Kleisli_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadPlus_288 -> () -> () -> ()
d_Kleisli_332 = erased
-- Effect.Monad.RawMonadPlus._.empty
d_empty_334 :: T_RawMonadPlus_288 -> () -> AgdaAny
d_empty_334 v0
  = coe
      MAlonzo.Code.Effect.Empty.d_empty_22
      (coe d_rawEmpty_218 (coe d_rawMonadZero_296 (coe v0)))
-- Effect.Monad.RawMonadPlus._.ignore
d_ignore_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadPlus_288 -> () -> AgdaAny -> AgdaAny
d_ignore_336 ~v0 ~v1 ~v2 v3 = du_ignore_336 v3
du_ignore_336 :: T_RawMonadPlus_288 -> () -> AgdaAny -> AgdaAny
du_ignore_336 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (let v2 = d_rawMonad_216 (coe v1) in
       coe
         (let v3 = d_rawApplicative_32 (coe v2) in
          coe
            (\ v4 ->
               coe
                 MAlonzo.Code.Effect.Functor.du_ignore_40
                 (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v3)))))
-- Effect.Monad.RawMonadPlus._.pure
d_pure_338 :: T_RawMonadPlus_288 -> () -> AgdaAny -> AgdaAny
d_pure_338 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_pure_32
      (coe
         d_rawApplicative_32
         (coe d_rawMonad_216 (coe d_rawMonadZero_296 (coe v0))))
-- Effect.Monad.RawMonadPlus._.rawApplicative
d_rawApplicative_340 ::
  T_RawMonadPlus_288 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_rawApplicative_340 v0
  = coe
      d_rawApplicative_32
      (coe d_rawMonad_216 (coe d_rawMonadZero_296 (coe v0)))
-- Effect.Monad.RawMonadPlus._.rawApplicativeZero
d_rawApplicativeZero_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicativeZero_122
d_rawApplicativeZero_342 ~v0 ~v1 ~v2 v3
  = du_rawApplicativeZero_342 v3
du_rawApplicativeZero_342 ::
  T_RawMonadPlus_288 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicativeZero_122
du_rawApplicativeZero_342 v0
  = coe du_rawApplicativeZero_278 (coe d_rawMonadZero_296 (coe v0))
-- Effect.Monad.RawMonadPlus._.rawEmpty
d_rawEmpty_344 ::
  T_RawMonadPlus_288 -> MAlonzo.Code.Effect.Empty.T_RawEmpty_16
d_rawEmpty_344 v0
  = coe d_rawEmpty_218 (coe d_rawMonadZero_296 (coe v0))
-- Effect.Monad.RawMonadPlus._.rawFunctor
d_rawFunctor_346 ::
  T_RawMonadPlus_288 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_346 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
      (coe
         d_rawApplicative_32
         (coe d_rawMonad_216 (coe d_rawMonadZero_296 (coe v0))))
-- Effect.Monad.RawMonadPlus._.rawMonad
d_rawMonad_348 :: T_RawMonadPlus_288 -> T_RawMonad_24
d_rawMonad_348 v0
  = coe d_rawMonad_216 (coe d_rawMonadZero_296 (coe v0))
-- Effect.Monad.RawMonadPlus._.return
d_return_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadPlus_288 -> () -> AgdaAny -> AgdaAny
d_return_350 ~v0 ~v1 ~v2 v3 = du_return_350 v3
du_return_350 :: T_RawMonadPlus_288 -> () -> AgdaAny -> AgdaAny
du_return_350 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (let v2 = d_rawMonad_216 (coe v1) in
       coe
         (\ v3 ->
            coe
              MAlonzo.Code.Effect.Applicative.du_return_68
              (coe d_rawApplicative_32 (coe v2))))
-- Effect.Monad.RawMonadPlus._.unless
d_unless_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadPlus_288 -> Bool -> AgdaAny -> AgdaAny
d_unless_352 ~v0 ~v1 ~v2 v3 = du_unless_352 v3
du_unless_352 :: T_RawMonadPlus_288 -> Bool -> AgdaAny -> AgdaAny
du_unless_352 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe (coe du_unless_96 (coe d_rawMonad_216 (coe v1)))
-- Effect.Monad.RawMonadPlus._.when
d_when_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadPlus_288 -> Bool -> AgdaAny -> AgdaAny
d_when_354 ~v0 ~v1 ~v2 v3 = du_when_354 v3
du_when_354 :: T_RawMonadPlus_288 -> Bool -> AgdaAny -> AgdaAny
du_when_354 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe (coe du_when_90 (coe d_rawMonad_216 (coe v1)))
-- Effect.Monad.RawMonadPlus._.zip
d_zip_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_356 ~v0 ~v1 ~v2 v3 = du_zip_356 v3
du_zip_356 ::
  T_RawMonadPlus_288 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_356 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (let v2 = d_rawMonad_216 (coe v1) in
       coe
         (\ v3 v4 ->
            coe
              MAlonzo.Code.Effect.Applicative.du_zip_66
              (coe d_rawApplicative_32 (coe v2))))
-- Effect.Monad.RawMonadPlus._.zipWith
d_zipWith_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_358 ~v0 ~v1 ~v2 v3 = du_zipWith_358 v3
du_zipWith_358 ::
  T_RawMonadPlus_288 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_358 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (let v2 = d_rawMonad_216 (coe v1) in
       coe
         (\ v3 v4 v5 v6 v7 v8 ->
            coe
              MAlonzo.Code.Effect.Applicative.du_zipWith_58
              (coe d_rawApplicative_32 (coe v2)) v6 v7 v8))
-- Effect.Monad.RawMonadPlus._.∅
d_'8709'_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawMonadPlus_288 -> () -> AgdaAny
d_'8709'_360 ~v0 ~v1 ~v2 v3 = du_'8709'_360 v3
du_'8709'_360 :: T_RawMonadPlus_288 -> () -> AgdaAny
du_'8709'_360 v0
  = let v1 = d_rawMonadZero_296 (coe v0) in
    coe
      (\ v2 ->
         coe
           MAlonzo.Code.Effect.Empty.du_'8709'_24
           (coe d_rawEmpty_218 (coe v1)))
-- Effect.Monad.RawMonadPlus._._<|>_
d__'60''124''62'__364 ::
  T_RawMonadPlus_288 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''124''62'__364 v0
  = coe
      MAlonzo.Code.Effect.Choice.d__'60''124''62'__22
      (coe d_rawChoice_298 (coe v0))
-- Effect.Monad.RawMonadPlus._._∣_
d__'8739'__366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8739'__366 ~v0 ~v1 ~v2 v3 = du__'8739'__366 v3
du__'8739'__366 ::
  T_RawMonadPlus_288 -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8739'__366 v0 v1
  = coe
      MAlonzo.Code.Effect.Choice.du__'8739'__24
      (coe d_rawChoice_298 (coe v0))
-- Effect.Monad.RawMonadPlus.rawAlternative
d_rawAlternative_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawMonadPlus_288 ->
  MAlonzo.Code.Effect.Applicative.T_RawAlternative_184
d_rawAlternative_368 ~v0 ~v1 ~v2 v3 = du_rawAlternative_368 v3
du_rawAlternative_368 ::
  T_RawMonadPlus_288 ->
  MAlonzo.Code.Effect.Applicative.T_RawAlternative_184
du_rawAlternative_368 v0
  = coe
      MAlonzo.Code.Effect.Applicative.C_constructor_246
      (coe du_rawApplicativeZero_278 (coe d_rawMonadZero_296 (coe v0)))
      (coe d_rawChoice_298 (coe v0))
-- Effect.Monad.RawMonadTd
d_RawMonadTd_382 a0 a1 a2 a3 a4 = ()
data T_RawMonadTd_382
  = C_constructor_448 (() -> AgdaAny -> AgdaAny) T_RawMonad_24
-- Effect.Monad.RawMonadTd.lift
d_lift_392 :: T_RawMonadTd_382 -> () -> AgdaAny -> AgdaAny
d_lift_392 v0
  = case coe v0 of
      C_constructor_448 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonadTd.rawMonad
d_rawMonad_394 :: T_RawMonadTd_382 -> T_RawMonad_24
d_rawMonad_394 v0
  = case coe v0 of
      C_constructor_448 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Monad.RawMonadTd._._*>_
d__'42''62'__398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__398 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'42''62'__398 v5
du__'42''62'__398 ::
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__398 v0
  = let v1 = d_rawMonad_394 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'42''62'__52
           (coe d_rawApplicative_32 (coe v1)) v4 v5)
-- Effect.Monad.RawMonadTd._._<$_
d__'60''36'__400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__400 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'60''36'__400 v5
du__'60''36'__400 ::
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__400 v0
  = let v1 = d_rawMonad_394 (coe v0) in
    coe
      (let v2 = d_rawApplicative_32 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Functor.du__'60''36'__32
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v2)) v5
              v6))
-- Effect.Monad.RawMonadTd._._<$>_
d__'60''36''62'__402 ::
  T_RawMonadTd_382 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__402 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe
         MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
         (coe d_rawApplicative_32 (coe d_rawMonad_394 (coe v0))))
-- Effect.Monad.RawMonadTd._._<&>_
d__'60''38''62'__404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_382 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__404 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du__'60''38''62'__404 v5
du__'60''38''62'__404 ::
  T_RawMonadTd_382 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__404 v0
  = let v1 = d_rawMonad_394 (coe v0) in
    coe
      (let v2 = d_rawApplicative_32 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v2)) v5
              v6))
-- Effect.Monad.RawMonadTd._._<*_
d__'60''42'__406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__406 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'60''42'__406 v5
du__'60''42'__406 ::
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__406 v0
  = let v1 = d_rawMonad_394 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'60''42'__46
           (coe d_rawApplicative_32 (coe v1)) v4 v5)
-- Effect.Monad.RawMonadTd._._<*>_
d__'60''42''62'__408 ::
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__408 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d__'60''42''62'__34
      (coe d_rawApplicative_32 (coe d_rawMonad_394 (coe v0)))
-- Effect.Monad.RawMonadTd._._<=<_
d__'60''61''60'__410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_382 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''61''60'__410 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du__'60''61''60'__410 v5
du__'60''61''60'__410 ::
  T_RawMonadTd_382 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''61''60'__410 v0 v1 v2 v3 v4 v5
  = coe du__'60''61''60'__88 (coe d_rawMonad_394 (coe v0)) v4 v5
-- Effect.Monad.RawMonadTd._._<⊛_
d__'60''8859'__412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__412 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'60''8859'__412 v5
du__'60''8859'__412 ::
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__412 v0
  = let v1 = d_rawMonad_394 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'60''8859'__72
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadTd._._=<<_
d__'61''60''60'__414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_382 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'61''60''60'__414 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du__'61''60''60'__414 v5
du__'61''60''60'__414 ::
  T_RawMonadTd_382 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'61''60''60'__414 v0 v1 v2 v3 v4
  = coe du__'61''60''60'__72 (coe d_rawMonad_394 (coe v0)) v3 v4
-- Effect.Monad.RawMonadTd._._>=>_
d__'62''61''62'__416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_382 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'62''61''62'__416 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du__'62''61''62'__416 v5
du__'62''61''62'__416 ::
  T_RawMonadTd_382 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'62''61''62'__416 v0 v1 v2 v3 v4 v5 v6
  = coe du__'62''61''62'__80 (coe d_rawMonad_394 (coe v0)) v4 v5 v6
-- Effect.Monad.RawMonadTd._._>>_
d__'62''62'__418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__418 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'62''62'__418 v5
du__'62''62'__418 ::
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__418 v0 v1 v2
  = coe du__'62''62'__70 (coe d_rawMonad_394 (coe v0))
-- Effect.Monad.RawMonadTd._._>>=_
d__'62''62''61'__420 ::
  T_RawMonadTd_382 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__420 v0
  = coe d__'62''62''61'__34 (coe d_rawMonad_394 (coe v0))
-- Effect.Monad.RawMonadTd._._⊗_
d__'8855'__422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__422 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'8855'__422 v5
du__'8855'__422 ::
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__422 v0
  = let v1 = d_rawMonad_394 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8855'__76
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadTd._._⊛_
d__'8859'__424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__424 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'8859'__424 v5
du__'8859'__424 ::
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__424 v0
  = let v1 = d_rawMonad_394 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8859'__70
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadTd._._⊛>_
d__'8859''62'__426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__426 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'8859''62'__426 v5
du__'8859''62'__426 ::
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__426 v0
  = let v1 = d_rawMonad_394 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8859''62'__74
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadTd._.Kleisli
d_Kleisli_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> (() -> ()) -> T_RawMonadTd_382 -> () -> () -> ()
d_Kleisli_428 = erased
-- Effect.Monad.RawMonadTd._.ignore
d_ignore_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) -> T_RawMonadTd_382 -> () -> AgdaAny -> AgdaAny
d_ignore_430 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_ignore_430 v5
du_ignore_430 :: T_RawMonadTd_382 -> () -> AgdaAny -> AgdaAny
du_ignore_430 v0
  = let v1 = d_rawMonad_394 (coe v0) in
    coe
      (let v2 = d_rawApplicative_32 (coe v1) in
       coe
         (\ v3 ->
            coe
              MAlonzo.Code.Effect.Functor.du_ignore_40
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v2))))
-- Effect.Monad.RawMonadTd._.pure
d_pure_432 :: T_RawMonadTd_382 -> () -> AgdaAny -> AgdaAny
d_pure_432 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_pure_32
      (coe d_rawApplicative_32 (coe d_rawMonad_394 (coe v0)))
-- Effect.Monad.RawMonadTd._.rawApplicative
d_rawApplicative_434 ::
  T_RawMonadTd_382 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_rawApplicative_434 v0
  = coe d_rawApplicative_32 (coe d_rawMonad_394 (coe v0))
-- Effect.Monad.RawMonadTd._.rawFunctor
d_rawFunctor_436 ::
  T_RawMonadTd_382 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_436 v0
  = coe
      MAlonzo.Code.Effect.Applicative.d_rawFunctor_30
      (coe d_rawApplicative_32 (coe d_rawMonad_394 (coe v0)))
-- Effect.Monad.RawMonadTd._.return
d_return_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) -> T_RawMonadTd_382 -> () -> AgdaAny -> AgdaAny
d_return_438 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_return_438 v5
du_return_438 :: T_RawMonadTd_382 -> () -> AgdaAny -> AgdaAny
du_return_438 v0
  = let v1 = d_rawMonad_394 (coe v0) in
    coe
      (\ v2 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_return_68
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadTd._.unless
d_unless_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) -> T_RawMonadTd_382 -> Bool -> AgdaAny -> AgdaAny
d_unless_440 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_unless_440 v5
du_unless_440 :: T_RawMonadTd_382 -> Bool -> AgdaAny -> AgdaAny
du_unless_440 v0 = coe du_unless_96 (coe d_rawMonad_394 (coe v0))
-- Effect.Monad.RawMonadTd._.when
d_when_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) -> T_RawMonadTd_382 -> Bool -> AgdaAny -> AgdaAny
d_when_442 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_when_442 v5
du_when_442 :: T_RawMonadTd_382 -> Bool -> AgdaAny -> AgdaAny
du_when_442 v0 = coe du_when_90 (coe d_rawMonad_394 (coe v0))
-- Effect.Monad.RawMonadTd._.zip
d_zip_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_444 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_zip_444 v5
du_zip_444 ::
  T_RawMonadTd_382 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_444 v0
  = let v1 = d_rawMonad_394 (coe v0) in
    coe
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_zip_66
           (coe d_rawApplicative_32 (coe v1)))
-- Effect.Monad.RawMonadTd._.zipWith
d_zipWith_446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawMonadTd_382 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_446 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_zipWith_446 v5
du_zipWith_446 ::
  T_RawMonadTd_382 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_446 v0
  = let v1 = d_rawMonad_394 (coe v0) in
    coe
      (\ v2 v3 v4 v5 v6 v7 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_zipWith_58
           (coe d_rawApplicative_32 (coe v1)) v5 v6 v7)
-- Effect.Monad.RawMonadT
d_RawMonadT_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((() -> ()) -> () -> ()) -> ()
d_RawMonadT_452 = erased
