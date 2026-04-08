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

module MAlonzo.Code.Effect.Applicative where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Effect.Choice
import qualified MAlonzo.Code.Effect.Empty
import qualified MAlonzo.Code.Effect.Functor
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Level

-- Effect.Applicative.RawApplicative
d_RawApplicative_20 a0 a1 a2 = ()
data T_RawApplicative_20
  = C_constructor_78 MAlonzo.Code.Effect.Functor.T_RawFunctor_24
                     (() -> AgdaAny -> AgdaAny)
                     (() -> () -> AgdaAny -> AgdaAny -> AgdaAny)
-- Effect.Applicative.RawApplicative.rawFunctor
d_rawFunctor_30 ::
  T_RawApplicative_20 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_30 v0
  = case coe v0 of
      C_constructor_78 v1 v2 v3 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.RawApplicative.pure
d_pure_32 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_pure_32 v0
  = case coe v0 of
      C_constructor_78 v1 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.RawApplicative._<*>_
d__'60''42''62'__34 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__34 v0
  = case coe v0 of
      C_constructor_78 v1 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.RawApplicative._._<$_
d__'60''36'__38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__38 ~v0 ~v1 ~v2 v3 = du__'60''36'__38 v3
du__'60''36'__38 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__38 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''36'__32
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.RawApplicative._._<$>_
d__'60''36''62'__40 ::
  T_RawApplicative_20 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__40 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.RawApplicative._._<&>_
d__'60''38''62'__42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__42 ~v0 ~v1 ~v2 v3 = du__'60''38''62'__42 v3
du__'60''38''62'__42 ::
  T_RawApplicative_20 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__42 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.RawApplicative._.ignore
d_ignore_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_ignore_44 ~v0 ~v1 ~v2 v3 = du_ignore_44 v3
du_ignore_44 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_ignore_44 v0 v1
  = coe
      MAlonzo.Code.Effect.Functor.du_ignore_40
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.RawApplicative._<*_
d__'60''42'__46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__46 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du__'60''42'__46 v3 v6 v7
du__'60''42'__46 ::
  T_RawApplicative_20 -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__46 v0 v1 v2
  = coe
      d__'60''42''62'__34 v0 erased erased
      (coe
         MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
         (d_rawFunctor_30 (coe v0)) erased erased (\ v3 v4 -> v3) v1)
      v2
-- Effect.Applicative.RawApplicative._*>_
d__'42''62'__52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__52 ~v0 ~v1 ~v2 v3 ~v4 ~v5 v6 v7
  = du__'42''62'__52 v3 v6 v7
du__'42''62'__52 ::
  T_RawApplicative_20 -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__52 v0 v1 v2
  = coe
      d__'60''42''62'__34 v0 erased erased
      (coe
         MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
         (d_rawFunctor_30 (coe v0)) erased erased (\ v3 v4 -> v4) v1)
      v2
-- Effect.Applicative.RawApplicative.zipWith
d_zipWith_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_58 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_zipWith_58 v3 v7 v8 v9
du_zipWith_58 ::
  T_RawApplicative_20 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_58 v0 v1 v2 v3
  = coe
      d__'60''42''62'__34 v0 erased erased
      (coe
         MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
         (d_rawFunctor_30 (coe v0)) erased erased v1 v2)
      v3
-- Effect.Applicative.RawApplicative.zip
d_zip_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_66 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du_zip_66 v3
du_zip_66 :: T_RawApplicative_20 -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_66 v0
  = coe
      du_zipWith_58 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32)
-- Effect.Applicative.RawApplicative.return
d_return_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_return_68 ~v0 ~v1 ~v2 v3 ~v4 = du_return_68 v3
du_return_68 :: T_RawApplicative_20 -> AgdaAny -> AgdaAny
du_return_68 v0 = coe d_pure_32 v0 erased
-- Effect.Applicative.RawApplicative._⊛_
d__'8859'__70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__70 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du__'8859'__70 v3
du__'8859'__70 ::
  T_RawApplicative_20 -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__70 v0 = coe d__'60''42''62'__34 v0 erased erased
-- Effect.Applicative.RawApplicative._<⊛_
d__'60''8859'__72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__72 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du__'60''8859'__72 v3
du__'60''8859'__72 ::
  T_RawApplicative_20 -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__72 v0 = coe du__'60''42'__46 (coe v0)
-- Effect.Applicative.RawApplicative._⊛>_
d__'8859''62'__74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__74 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du__'8859''62'__74 v3
du__'8859''62'__74 ::
  T_RawApplicative_20 -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__74 v0 = coe du__'42''62'__52 (coe v0)
-- Effect.Applicative.RawApplicative._⊗_
d__'8855'__76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__76 ~v0 ~v1 ~v2 v3 ~v4 ~v5 = du__'8855'__76 v3
du__'8855'__76 ::
  T_RawApplicative_20 -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__76 v0 = coe du_zip_66 (coe v0)
-- Effect.Applicative._.mkRawApplicative
d_mkRawApplicative_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> AgdaAny -> AgdaAny) ->
  (() -> () -> AgdaAny -> AgdaAny -> AgdaAny) -> T_RawApplicative_20
d_mkRawApplicative_96 ~v0 ~v1 ~v2 v3 v4
  = du_mkRawApplicative_96 v3 v4
du_mkRawApplicative_96 ::
  (() -> AgdaAny -> AgdaAny) ->
  (() -> () -> AgdaAny -> AgdaAny -> AgdaAny) -> T_RawApplicative_20
du_mkRawApplicative_96 v0 v1
  = coe
      C_constructor_78
      (coe
         MAlonzo.Code.Effect.Functor.C_constructor_44
         (coe
            (\ v2 v3 ->
               coe
                 MAlonzo.Code.Function.Base.du__'8728''8242'__216 (coe v1 v2 v3)
                 (coe v0 ()))))
      (coe (\ v2 -> coe v0 v2)) (coe (\ v2 v3 -> coe v1 v2 v3))
-- Effect.Applicative.RawApplicativeZero
d_RawApplicativeZero_122 a0 a1 a2 = ()
data T_RawApplicativeZero_122
  = C_constructor_176 T_RawApplicative_20
                      MAlonzo.Code.Effect.Empty.T_RawEmpty_16
-- Effect.Applicative.RawApplicativeZero.rawApplicative
d_rawApplicative_130 ::
  T_RawApplicativeZero_122 -> T_RawApplicative_20
d_rawApplicative_130 v0
  = case coe v0 of
      C_constructor_176 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.RawApplicativeZero.rawEmpty
d_rawEmpty_132 ::
  T_RawApplicativeZero_122 -> MAlonzo.Code.Effect.Empty.T_RawEmpty_16
d_rawEmpty_132 v0
  = case coe v0 of
      C_constructor_176 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.RawApplicativeZero._._*>_
d__'42''62'__136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__136 ~v0 ~v1 ~v2 v3 = du__'42''62'__136 v3
du__'42''62'__136 ::
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__136 v0 v1 v2 v3 v4
  = coe du__'42''62'__52 (coe d_rawApplicative_130 (coe v0)) v3 v4
-- Effect.Applicative.RawApplicativeZero._._<$_
d__'60''36'__138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__138 ~v0 ~v1 ~v2 v3 = du__'60''36'__138 v3
du__'60''36'__138 ::
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__138 v0
  = let v1 = d_rawApplicative_130 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Functor.du__'60''36'__32
           (coe d_rawFunctor_30 (coe v1)) v4 v5)
-- Effect.Applicative.RawApplicativeZero._._<$>_
d__'60''36''62'__140 ::
  T_RawApplicativeZero_122 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__140 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe d_rawFunctor_30 (coe d_rawApplicative_130 (coe v0)))
-- Effect.Applicative.RawApplicativeZero._._<&>_
d__'60''38''62'__142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__142 ~v0 ~v1 ~v2 v3 = du__'60''38''62'__142 v3
du__'60''38''62'__142 ::
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__142 v0
  = let v1 = d_rawApplicative_130 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
           (coe d_rawFunctor_30 (coe v1)) v4 v5)
-- Effect.Applicative.RawApplicativeZero._._<*_
d__'60''42'__144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__144 ~v0 ~v1 ~v2 v3 = du__'60''42'__144 v3
du__'60''42'__144 ::
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__144 v0 v1 v2 v3 v4
  = coe du__'60''42'__46 (coe d_rawApplicative_130 (coe v0)) v3 v4
-- Effect.Applicative.RawApplicativeZero._._<*>_
d__'60''42''62'__146 ::
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__146 v0
  = coe d__'60''42''62'__34 (coe d_rawApplicative_130 (coe v0))
-- Effect.Applicative.RawApplicativeZero._._<⊛_
d__'60''8859'__148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__148 ~v0 ~v1 ~v2 v3 = du__'60''8859'__148 v3
du__'60''8859'__148 ::
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__148 v0 v1 v2
  = coe du__'60''8859'__72 (coe d_rawApplicative_130 (coe v0))
-- Effect.Applicative.RawApplicativeZero._._⊗_
d__'8855'__150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__150 ~v0 ~v1 ~v2 v3 = du__'8855'__150 v3
du__'8855'__150 ::
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__150 v0 v1 v2
  = coe du__'8855'__76 (coe d_rawApplicative_130 (coe v0))
-- Effect.Applicative.RawApplicativeZero._._⊛_
d__'8859'__152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__152 ~v0 ~v1 ~v2 v3 = du__'8859'__152 v3
du__'8859'__152 ::
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__152 v0 v1 v2
  = coe du__'8859'__70 (coe d_rawApplicative_130 (coe v0))
-- Effect.Applicative.RawApplicativeZero._._⊛>_
d__'8859''62'__154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__154 ~v0 ~v1 ~v2 v3 = du__'8859''62'__154 v3
du__'8859''62'__154 ::
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__154 v0 v1 v2
  = coe du__'8859''62'__74 (coe d_rawApplicative_130 (coe v0))
-- Effect.Applicative.RawApplicativeZero._.ignore
d_ignore_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawApplicativeZero_122 -> () -> AgdaAny -> AgdaAny
d_ignore_156 ~v0 ~v1 ~v2 v3 = du_ignore_156 v3
du_ignore_156 ::
  T_RawApplicativeZero_122 -> () -> AgdaAny -> AgdaAny
du_ignore_156 v0
  = let v1 = d_rawApplicative_130 (coe v0) in
    coe
      (\ v2 ->
         coe
           MAlonzo.Code.Effect.Functor.du_ignore_40
           (coe d_rawFunctor_30 (coe v1)))
-- Effect.Applicative.RawApplicativeZero._.pure
d_pure_158 :: T_RawApplicativeZero_122 -> () -> AgdaAny -> AgdaAny
d_pure_158 v0 = coe d_pure_32 (coe d_rawApplicative_130 (coe v0))
-- Effect.Applicative.RawApplicativeZero._.rawFunctor
d_rawFunctor_160 ::
  T_RawApplicativeZero_122 ->
  MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_160 v0
  = coe d_rawFunctor_30 (coe d_rawApplicative_130 (coe v0))
-- Effect.Applicative.RawApplicativeZero._.return
d_return_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawApplicativeZero_122 -> () -> AgdaAny -> AgdaAny
d_return_162 ~v0 ~v1 ~v2 v3 = du_return_162 v3
du_return_162 ::
  T_RawApplicativeZero_122 -> () -> AgdaAny -> AgdaAny
du_return_162 v0 v1
  = coe du_return_68 (coe d_rawApplicative_130 (coe v0))
-- Effect.Applicative.RawApplicativeZero._.zip
d_zip_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_164 ~v0 ~v1 ~v2 v3 = du_zip_164 v3
du_zip_164 ::
  T_RawApplicativeZero_122 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_164 v0 v1 v2
  = coe du_zip_66 (coe d_rawApplicative_130 (coe v0))
-- Effect.Applicative.RawApplicativeZero._.zipWith
d_zipWith_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_122 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_166 ~v0 ~v1 ~v2 v3 = du_zipWith_166 v3
du_zipWith_166 ::
  T_RawApplicativeZero_122 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_166 v0 v1 v2 v3 v4 v5 v6
  = coe du_zipWith_58 (coe d_rawApplicative_130 (coe v0)) v4 v5 v6
-- Effect.Applicative.RawApplicativeZero._.empty
d_empty_170 :: T_RawApplicativeZero_122 -> () -> AgdaAny
d_empty_170 v0
  = coe
      MAlonzo.Code.Effect.Empty.d_empty_22 (coe d_rawEmpty_132 (coe v0))
-- Effect.Applicative.RawApplicativeZero._.∅
d_'8709'_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawApplicativeZero_122 -> () -> AgdaAny
d_'8709'_172 ~v0 ~v1 ~v2 v3 = du_'8709'_172 v3
du_'8709'_172 :: T_RawApplicativeZero_122 -> () -> AgdaAny
du_'8709'_172 v0 v1
  = coe
      MAlonzo.Code.Effect.Empty.du_'8709'_24
      (coe d_rawEmpty_132 (coe v0))
-- Effect.Applicative.RawApplicativeZero.guard
d_guard_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawApplicativeZero_122 -> Bool -> AgdaAny
d_guard_174 ~v0 ~v1 ~v2 v3 v4 = du_guard_174 v3 v4
du_guard_174 :: T_RawApplicativeZero_122 -> Bool -> AgdaAny
du_guard_174 v0 v1
  = if coe v1
      then coe
             d_pure_32 (d_rawApplicative_130 (coe v0)) erased
             (coe
                MAlonzo.Code.Level.C_lift_20
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      else coe
             MAlonzo.Code.Effect.Empty.d_empty_22 (d_rawEmpty_132 (coe v0))
             erased
-- Effect.Applicative.RawAlternative
d_RawAlternative_184 a0 a1 a2 = ()
data T_RawAlternative_184
  = C_constructor_246 T_RawApplicativeZero_122
                      MAlonzo.Code.Effect.Choice.T_RawChoice_16
-- Effect.Applicative.RawAlternative.rawApplicativeZero
d_rawApplicativeZero_192 ::
  T_RawAlternative_184 -> T_RawApplicativeZero_122
d_rawApplicativeZero_192 v0
  = case coe v0 of
      C_constructor_246 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.RawAlternative.rawChoice
d_rawChoice_194 ::
  T_RawAlternative_184 -> MAlonzo.Code.Effect.Choice.T_RawChoice_16
d_rawChoice_194 v0
  = case coe v0 of
      C_constructor_246 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.RawAlternative._._*>_
d__'42''62'__198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__198 ~v0 ~v1 ~v2 v3 = du__'42''62'__198 v3
du__'42''62'__198 ::
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__198 v0
  = let v1 = d_rawApplicativeZero_192 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe du__'42''62'__52 (coe d_rawApplicative_130 (coe v1)) v4 v5)
-- Effect.Applicative.RawAlternative._._<$_
d__'60''36'__200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__200 ~v0 ~v1 ~v2 v3 = du__'60''36'__200 v3
du__'60''36'__200 ::
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__200 v0
  = let v1 = d_rawApplicativeZero_192 (coe v0) in
    coe
      (let v2 = d_rawApplicative_130 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Functor.du__'60''36'__32
              (coe d_rawFunctor_30 (coe v2)) v5 v6))
-- Effect.Applicative.RawAlternative._._<$>_
d__'60''36''62'__202 ::
  T_RawAlternative_184 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__202 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe
         d_rawFunctor_30
         (coe d_rawApplicative_130 (coe d_rawApplicativeZero_192 (coe v0))))
-- Effect.Applicative.RawAlternative._._<&>_
d__'60''38''62'__204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_184 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__204 ~v0 ~v1 ~v2 v3 = du__'60''38''62'__204 v3
du__'60''38''62'__204 ::
  T_RawAlternative_184 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__204 v0
  = let v1 = d_rawApplicativeZero_192 (coe v0) in
    coe
      (let v2 = d_rawApplicative_130 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
              (coe d_rawFunctor_30 (coe v2)) v5 v6))
-- Effect.Applicative.RawAlternative._._<*_
d__'60''42'__206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__206 ~v0 ~v1 ~v2 v3 = du__'60''42'__206 v3
du__'60''42'__206 ::
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__206 v0
  = let v1 = d_rawApplicativeZero_192 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe du__'60''42'__46 (coe d_rawApplicative_130 (coe v1)) v4 v5)
-- Effect.Applicative.RawAlternative._._<*>_
d__'60''42''62'__208 ::
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__208 v0
  = coe
      d__'60''42''62'__34
      (coe d_rawApplicative_130 (coe d_rawApplicativeZero_192 (coe v0)))
-- Effect.Applicative.RawAlternative._._<⊛_
d__'60''8859'__210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__210 ~v0 ~v1 ~v2 v3 = du__'60''8859'__210 v3
du__'60''8859'__210 ::
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__210 v0
  = let v1 = d_rawApplicativeZero_192 (coe v0) in
    coe
      (\ v2 v3 ->
         coe du__'60''8859'__72 (coe d_rawApplicative_130 (coe v1)))
-- Effect.Applicative.RawAlternative._._⊗_
d__'8855'__212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__212 ~v0 ~v1 ~v2 v3 = du__'8855'__212 v3
du__'8855'__212 ::
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__212 v0
  = let v1 = d_rawApplicativeZero_192 (coe v0) in
    coe
      (\ v2 v3 -> coe du__'8855'__76 (coe d_rawApplicative_130 (coe v1)))
-- Effect.Applicative.RawAlternative._._⊛_
d__'8859'__214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__214 ~v0 ~v1 ~v2 v3 = du__'8859'__214 v3
du__'8859'__214 ::
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__214 v0
  = let v1 = d_rawApplicativeZero_192 (coe v0) in
    coe
      (\ v2 v3 -> coe du__'8859'__70 (coe d_rawApplicative_130 (coe v1)))
-- Effect.Applicative.RawAlternative._._⊛>_
d__'8859''62'__216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__216 ~v0 ~v1 ~v2 v3 = du__'8859''62'__216 v3
du__'8859''62'__216 ::
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__216 v0
  = let v1 = d_rawApplicativeZero_192 (coe v0) in
    coe
      (\ v2 v3 ->
         coe du__'8859''62'__74 (coe d_rawApplicative_130 (coe v1)))
-- Effect.Applicative.RawAlternative._.empty
d_empty_218 :: T_RawAlternative_184 -> () -> AgdaAny
d_empty_218 v0
  = coe
      MAlonzo.Code.Effect.Empty.d_empty_22
      (coe d_rawEmpty_132 (coe d_rawApplicativeZero_192 (coe v0)))
-- Effect.Applicative.RawAlternative._.guard
d_guard_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawAlternative_184 -> Bool -> AgdaAny
d_guard_220 ~v0 ~v1 ~v2 v3 = du_guard_220 v3
du_guard_220 :: T_RawAlternative_184 -> Bool -> AgdaAny
du_guard_220 v0
  = coe du_guard_174 (coe d_rawApplicativeZero_192 (coe v0))
-- Effect.Applicative.RawAlternative._.ignore
d_ignore_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawAlternative_184 -> () -> AgdaAny -> AgdaAny
d_ignore_222 ~v0 ~v1 ~v2 v3 = du_ignore_222 v3
du_ignore_222 :: T_RawAlternative_184 -> () -> AgdaAny -> AgdaAny
du_ignore_222 v0
  = let v1 = d_rawApplicativeZero_192 (coe v0) in
    coe
      (let v2 = d_rawApplicative_130 (coe v1) in
       coe
         (\ v3 ->
            coe
              MAlonzo.Code.Effect.Functor.du_ignore_40
              (coe d_rawFunctor_30 (coe v2))))
-- Effect.Applicative.RawAlternative._.pure
d_pure_224 :: T_RawAlternative_184 -> () -> AgdaAny -> AgdaAny
d_pure_224 v0
  = coe
      d_pure_32
      (coe d_rawApplicative_130 (coe d_rawApplicativeZero_192 (coe v0)))
-- Effect.Applicative.RawAlternative._.rawApplicative
d_rawApplicative_226 :: T_RawAlternative_184 -> T_RawApplicative_20
d_rawApplicative_226 v0
  = coe d_rawApplicative_130 (coe d_rawApplicativeZero_192 (coe v0))
-- Effect.Applicative.RawAlternative._.rawEmpty
d_rawEmpty_228 ::
  T_RawAlternative_184 -> MAlonzo.Code.Effect.Empty.T_RawEmpty_16
d_rawEmpty_228 v0
  = coe d_rawEmpty_132 (coe d_rawApplicativeZero_192 (coe v0))
-- Effect.Applicative.RawAlternative._.rawFunctor
d_rawFunctor_230 ::
  T_RawAlternative_184 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_230 v0
  = coe
      d_rawFunctor_30
      (coe d_rawApplicative_130 (coe d_rawApplicativeZero_192 (coe v0)))
-- Effect.Applicative.RawAlternative._.return
d_return_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawAlternative_184 -> () -> AgdaAny -> AgdaAny
d_return_232 ~v0 ~v1 ~v2 v3 = du_return_232 v3
du_return_232 :: T_RawAlternative_184 -> () -> AgdaAny -> AgdaAny
du_return_232 v0
  = let v1 = d_rawApplicativeZero_192 (coe v0) in
    coe (\ v2 -> coe du_return_68 (coe d_rawApplicative_130 (coe v1)))
-- Effect.Applicative.RawAlternative._.zip
d_zip_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_234 ~v0 ~v1 ~v2 v3 = du_zip_234 v3
du_zip_234 ::
  T_RawAlternative_184 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_234 v0
  = let v1 = d_rawApplicativeZero_192 (coe v0) in
    coe (\ v2 v3 -> coe du_zip_66 (coe d_rawApplicative_130 (coe v1)))
-- Effect.Applicative.RawAlternative._.zipWith
d_zipWith_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_184 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_236 ~v0 ~v1 ~v2 v3 = du_zipWith_236 v3
du_zipWith_236 ::
  T_RawAlternative_184 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_236 v0
  = let v1 = d_rawApplicativeZero_192 (coe v0) in
    coe
      (\ v2 v3 v4 v5 v6 v7 ->
         coe du_zipWith_58 (coe d_rawApplicative_130 (coe v1)) v5 v6 v7)
-- Effect.Applicative.RawAlternative._.∅
d_'8709'_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawAlternative_184 -> () -> AgdaAny
d_'8709'_238 ~v0 ~v1 ~v2 v3 = du_'8709'_238 v3
du_'8709'_238 :: T_RawAlternative_184 -> () -> AgdaAny
du_'8709'_238 v0
  = let v1 = d_rawApplicativeZero_192 (coe v0) in
    coe
      (\ v2 ->
         coe
           MAlonzo.Code.Effect.Empty.du_'8709'_24
           (coe d_rawEmpty_132 (coe v1)))
-- Effect.Applicative.RawAlternative._._<|>_
d__'60''124''62'__242 ::
  T_RawAlternative_184 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''124''62'__242 v0
  = coe
      MAlonzo.Code.Effect.Choice.d__'60''124''62'__22
      (coe d_rawChoice_194 (coe v0))
-- Effect.Applicative.RawAlternative._._∣_
d__'8739'__244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_184 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8739'__244 ~v0 ~v1 ~v2 v3 = du__'8739'__244 v3
du__'8739'__244 ::
  T_RawAlternative_184 -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8739'__244 v0 v1
  = coe
      MAlonzo.Code.Effect.Choice.du__'8739'__24
      (coe d_rawChoice_194 (coe v0))
-- Effect.Applicative.Morphism
d_Morphism_260 a0 a1 a2 a3 a4 a5 = ()
newtype T_Morphism_260
  = C_constructor_444 MAlonzo.Code.Effect.Functor.T_Morphism_60
-- Effect.Applicative.A₁._*>_
d__'42''62'__272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__272 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'42''62'__272 v4
du__'42''62'__272 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__272 v0 v1 v2 v3 v4
  = coe du__'42''62'__52 (coe v0) v3 v4
-- Effect.Applicative.A₁._<$_
d__'60''36'__274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__274 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'60''36'__274 v4
du__'60''36'__274 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__274 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''36'__32
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.A₁._<$>_
d__'60''36''62'__276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__276 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du__'60''36''62'__276 v4
du__'60''36''62'__276 ::
  T_RawApplicative_20 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62'__276 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.A₁._<&>_
d__'60''38''62'__278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__278 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du__'60''38''62'__278 v4
du__'60''38''62'__278 ::
  T_RawApplicative_20 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__278 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.A₁._<*_
d__'60''42'__280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__280 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'60''42'__280 v4
du__'60''42'__280 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__280 v0 v1 v2 v3 v4
  = coe du__'60''42'__46 (coe v0) v3 v4
-- Effect.Applicative.A₁._<*>_
d__'60''42''62'__282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__282 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du__'60''42''62'__282 v4
du__'60''42''62'__282 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42''62'__282 v0 = coe d__'60''42''62'__34 (coe v0)
-- Effect.Applicative.A₁._<⊛_
d__'60''8859'__284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__284 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'60''8859'__284 v4
du__'60''8859'__284 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__284 v0 v1 v2 = coe du__'60''8859'__72 (coe v0)
-- Effect.Applicative.A₁._⊗_
d__'8855'__286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__286 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8855'__286 v4
du__'8855'__286 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__286 v0 v1 v2 = coe du__'8855'__76 (coe v0)
-- Effect.Applicative.A₁._⊛_
d__'8859'__288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__288 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8859'__288 v4
du__'8859'__288 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__288 v0 v1 v2 = coe du__'8859'__70 (coe v0)
-- Effect.Applicative.A₁._⊛>_
d__'8859''62'__290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__290 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8859''62'__290 v4
du__'8859''62'__290 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__290 v0 v1 v2 = coe du__'8859''62'__74 (coe v0)
-- Effect.Applicative.A₁.ignore
d_ignore_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_ignore_292 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_ignore_292 v4
du_ignore_292 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_ignore_292 v0 v1
  = coe
      MAlonzo.Code.Effect.Functor.du_ignore_40
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.A₁.pure
d_pure_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_pure_294 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_pure_294 v4
du_pure_294 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_pure_294 v0 = coe d_pure_32 (coe v0)
-- Effect.Applicative.A₁.rawFunctor
d_rawFunctor_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_296 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_rawFunctor_296 v4
du_rawFunctor_296 ::
  T_RawApplicative_20 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
du_rawFunctor_296 v0 = coe d_rawFunctor_30 (coe v0)
-- Effect.Applicative.A₁.return
d_return_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_return_298 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_return_298 v4
du_return_298 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_return_298 v0 v1 = coe du_return_68 (coe v0)
-- Effect.Applicative.A₁.zip
d_zip_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_300 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_zip_300 v4
du_zip_300 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_300 v0 v1 v2 = coe du_zip_66 (coe v0)
-- Effect.Applicative.A₁.zipWith
d_zipWith_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_302 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_zipWith_302 v4
du_zipWith_302 ::
  T_RawApplicative_20 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_302 v0 v1 v2 v3 v4 v5 v6
  = coe du_zipWith_58 (coe v0) v4 v5 v6
-- Effect.Applicative.A₂._*>_
d__'42''62'__306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__306 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'42''62'__306 v5
du__'42''62'__306 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__306 v0 v1 v2 v3 v4
  = coe du__'42''62'__52 (coe v0) v3 v4
-- Effect.Applicative.A₂._<$_
d__'60''36'__308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__308 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'60''36'__308 v5
du__'60''36'__308 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__308 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''36'__32
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.A₂._<$>_
d__'60''36''62'__310 ::
  T_RawApplicative_20 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__310 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.A₂._<&>_
d__'60''38''62'__312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__312 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du__'60''38''62'__312 v5
du__'60''38''62'__312 ::
  T_RawApplicative_20 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__312 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.A₂._<*_
d__'60''42'__314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__314 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'60''42'__314 v5
du__'60''42'__314 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__314 v0 v1 v2 v3 v4
  = coe du__'60''42'__46 (coe v0) v3 v4
-- Effect.Applicative.A₂._<*>_
d__'60''42''62'__316 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__316 v0 = coe d__'60''42''62'__34 (coe v0)
-- Effect.Applicative.A₂._<⊛_
d__'60''8859'__318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__318 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'60''8859'__318 v5
du__'60''8859'__318 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__318 v0 v1 v2 = coe du__'60''8859'__72 (coe v0)
-- Effect.Applicative.A₂._⊗_
d__'8855'__320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__320 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'8855'__320 v5
du__'8855'__320 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__320 v0 v1 v2 = coe du__'8855'__76 (coe v0)
-- Effect.Applicative.A₂._⊛_
d__'8859'__322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__322 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'8859'__322 v5
du__'8859'__322 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__322 v0 v1 v2 = coe du__'8859'__70 (coe v0)
-- Effect.Applicative.A₂._⊛>_
d__'8859''62'__324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__324 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'8859''62'__324 v5
du__'8859''62'__324 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__324 v0 v1 v2 = coe du__'8859''62'__74 (coe v0)
-- Effect.Applicative.A₂.ignore
d_ignore_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_ignore_326 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_ignore_326 v5
du_ignore_326 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_ignore_326 v0 v1
  = coe
      MAlonzo.Code.Effect.Functor.du_ignore_40
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.A₂.pure
d_pure_328 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_pure_328 v0 = coe d_pure_32 (coe v0)
-- Effect.Applicative.A₂.rawFunctor
d_rawFunctor_330 ::
  T_RawApplicative_20 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_330 v0 = coe d_rawFunctor_30 (coe v0)
-- Effect.Applicative.A₂.return
d_return_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_return_332 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_return_332 v5
du_return_332 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_return_332 v0 v1 = coe du_return_68 (coe v0)
-- Effect.Applicative.A₂.zip
d_zip_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_334 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_zip_334 v5
du_zip_334 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_334 v0 v1 v2 = coe du_zip_66 (coe v0)
-- Effect.Applicative.A₂.zipWith
d_zipWith_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_336 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_zipWith_336 v5
du_zipWith_336 ::
  T_RawApplicative_20 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_336 v0 v1 v2 v3 v4 v5 v6
  = coe du_zipWith_58 (coe v0) v4 v5 v6
-- Effect.Applicative.Morphism.A₁._*>_
d__'42''62'__358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__358 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du__'42''62'__358 v4
du__'42''62'__358 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__358 v0 v1 v2 v3 v4
  = coe du__'42''62'__52 (coe v0) v3 v4
-- Effect.Applicative.Morphism.A₁._<$_
d__'60''36'__360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__360 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du__'60''36'__360 v4
du__'60''36'__360 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__360 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''36'__32
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.Morphism.A₁._<$>_
d__'60''36''62'__362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__362 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du__'60''36''62'__362 v4
du__'60''36''62'__362 ::
  T_RawApplicative_20 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62'__362 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.Morphism.A₁._<&>_
d__'60''38''62'__364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__364 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du__'60''38''62'__364 v4
du__'60''38''62'__364 ::
  T_RawApplicative_20 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__364 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.Morphism.A₁._<*_
d__'60''42'__366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__366 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du__'60''42'__366 v4
du__'60''42'__366 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__366 v0 v1 v2 v3 v4
  = coe du__'60''42'__46 (coe v0) v3 v4
-- Effect.Applicative.Morphism.A₁._<*>_
d__'60''42''62'__368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__368 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du__'60''42''62'__368 v4
du__'60''42''62'__368 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42''62'__368 v0 = coe d__'60''42''62'__34 (coe v0)
-- Effect.Applicative.Morphism.A₁._<⊛_
d__'60''8859'__370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__370 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du__'60''8859'__370 v4
du__'60''8859'__370 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__370 v0 v1 v2 = coe du__'60''8859'__72 (coe v0)
-- Effect.Applicative.Morphism.A₁._⊗_
d__'8855'__372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__372 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du__'8855'__372 v4
du__'8855'__372 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__372 v0 v1 v2 = coe du__'8855'__76 (coe v0)
-- Effect.Applicative.Morphism.A₁._⊛_
d__'8859'__374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__374 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du__'8859'__374 v4
du__'8859'__374 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__374 v0 v1 v2 = coe du__'8859'__70 (coe v0)
-- Effect.Applicative.Morphism.A₁._⊛>_
d__'8859''62'__376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__376 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du__'8859''62'__376 v4
du__'8859''62'__376 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__376 v0 v1 v2 = coe du__'8859''62'__74 (coe v0)
-- Effect.Applicative.Morphism.A₁.ignore
d_ignore_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> T_Morphism_260 -> () -> AgdaAny -> AgdaAny
d_ignore_378 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_ignore_378 v4
du_ignore_378 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_ignore_378 v0 v1
  = coe
      MAlonzo.Code.Effect.Functor.du_ignore_40
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.Morphism.A₁.pure
d_pure_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> T_Morphism_260 -> () -> AgdaAny -> AgdaAny
d_pure_380 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_pure_380 v4
du_pure_380 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_pure_380 v0 = coe d_pure_32 (coe v0)
-- Effect.Applicative.Morphism.A₁.rawFunctor
d_rawFunctor_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_382 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_rawFunctor_382 v4
du_rawFunctor_382 ::
  T_RawApplicative_20 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
du_rawFunctor_382 v0 = coe d_rawFunctor_30 (coe v0)
-- Effect.Applicative.Morphism.A₁.return
d_return_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> T_Morphism_260 -> () -> AgdaAny -> AgdaAny
d_return_384 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_return_384 v4
du_return_384 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_return_384 v0 v1 = coe du_return_68 (coe v0)
-- Effect.Applicative.Morphism.A₁.zip
d_zip_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_386 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_zip_386 v4
du_zip_386 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_386 v0 v1 v2 = coe du_zip_66 (coe v0)
-- Effect.Applicative.Morphism.A₁.zipWith
d_zipWith_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_388 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_zipWith_388 v4
du_zipWith_388 ::
  T_RawApplicative_20 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_388 v0 v1 v2 v3 v4 v5 v6
  = coe du_zipWith_58 (coe v0) v4 v5 v6
-- Effect.Applicative.Morphism.A₂._*>_
d__'42''62'__392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__392 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du__'42''62'__392 v5
du__'42''62'__392 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__392 v0 v1 v2 v3 v4
  = coe du__'42''62'__52 (coe v0) v3 v4
-- Effect.Applicative.Morphism.A₂._<$_
d__'60''36'__394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__394 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du__'60''36'__394 v5
du__'60''36'__394 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__394 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''36'__32
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.Morphism.A₂._<$>_
d__'60''36''62'__396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__396 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du__'60''36''62'__396 v5
du__'60''36''62'__396 ::
  T_RawApplicative_20 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62'__396 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.Morphism.A₂._<&>_
d__'60''38''62'__398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__398 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du__'60''38''62'__398 v5
du__'60''38''62'__398 ::
  T_RawApplicative_20 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__398 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.Morphism.A₂._<*_
d__'60''42'__400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__400 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du__'60''42'__400 v5
du__'60''42'__400 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__400 v0 v1 v2 v3 v4
  = coe du__'60''42'__46 (coe v0) v3 v4
-- Effect.Applicative.Morphism.A₂._<*>_
d__'60''42''62'__402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__402 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du__'60''42''62'__402 v5
du__'60''42''62'__402 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42''62'__402 v0 = coe d__'60''42''62'__34 (coe v0)
-- Effect.Applicative.Morphism.A₂._<⊛_
d__'60''8859'__404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__404 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du__'60''8859'__404 v5
du__'60''8859'__404 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__404 v0 v1 v2 = coe du__'60''8859'__72 (coe v0)
-- Effect.Applicative.Morphism.A₂._⊗_
d__'8855'__406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__406 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du__'8855'__406 v5
du__'8855'__406 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__406 v0 v1 v2 = coe du__'8855'__76 (coe v0)
-- Effect.Applicative.Morphism.A₂._⊛_
d__'8859'__408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__408 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du__'8859'__408 v5
du__'8859'__408 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__408 v0 v1 v2 = coe du__'8859'__70 (coe v0)
-- Effect.Applicative.Morphism.A₂._⊛>_
d__'8859''62'__410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__410 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du__'8859''62'__410 v5
du__'8859''62'__410 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__410 v0 v1 v2 = coe du__'8859''62'__74 (coe v0)
-- Effect.Applicative.Morphism.A₂.ignore
d_ignore_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> T_Morphism_260 -> () -> AgdaAny -> AgdaAny
d_ignore_412 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_ignore_412 v5
du_ignore_412 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_ignore_412 v0 v1
  = coe
      MAlonzo.Code.Effect.Functor.du_ignore_40
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.Morphism.A₂.pure
d_pure_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> T_Morphism_260 -> () -> AgdaAny -> AgdaAny
d_pure_414 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_pure_414 v5
du_pure_414 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_pure_414 v0 = coe d_pure_32 (coe v0)
-- Effect.Applicative.Morphism.A₂.rawFunctor
d_rawFunctor_416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_416 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_rawFunctor_416 v5
du_rawFunctor_416 ::
  T_RawApplicative_20 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
du_rawFunctor_416 v0 = coe d_rawFunctor_30 (coe v0)
-- Effect.Applicative.Morphism.A₂.return
d_return_418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> T_Morphism_260 -> () -> AgdaAny -> AgdaAny
d_return_418 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_return_418 v5
du_return_418 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_return_418 v0 v1 = coe du_return_68 (coe v0)
-- Effect.Applicative.Morphism.A₂.zip
d_zip_420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_420 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_zip_420 v5
du_zip_420 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_420 v0 v1 v2 = coe du_zip_66 (coe v0)
-- Effect.Applicative.Morphism.A₂.zipWith
d_zipWith_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_422 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_zipWith_422 v5
du_zipWith_422 ::
  T_RawApplicative_20 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_422 v0 v1 v2 v3 v4 v5 v6
  = coe du_zipWith_58 (coe v0) v4 v5 v6
-- Effect.Applicative.Morphism.functorMorphism
d_functorMorphism_424 ::
  T_Morphism_260 -> MAlonzo.Code.Effect.Functor.T_Morphism_60
d_functorMorphism_424 v0
  = case coe v0 of
      C_constructor_444 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.Morphism._.op
d_op_428 :: T_Morphism_260 -> () -> AgdaAny -> AgdaAny
d_op_428 v0
  = coe
      MAlonzo.Code.Effect.Functor.d_op_78
      (coe d_functorMorphism_424 (coe v0))
-- Effect.Applicative.Morphism._.op-<$>
d_op'45''60''36''62'_430 ::
  T_Morphism_260 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45''60''36''62'_430 = erased
-- Effect.Applicative.Morphism.op-pure
d_op'45'pure_434 ::
  T_Morphism_260 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45'pure_434 = erased
-- Effect.Applicative.Morphism.op-<*>
d_op'45''60''42''62'_440 ::
  T_Morphism_260 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45''60''42''62'_440 = erased
-- Effect.Applicative.Morphism.op-⊛
d_op'45''8859'_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_260 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45''8859'_442 = erased
