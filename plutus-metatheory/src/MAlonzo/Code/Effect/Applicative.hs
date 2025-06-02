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

module MAlonzo.Code.Effect.Applicative where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Effect.Choice qualified
import MAlonzo.Code.Effect.Empty qualified
import MAlonzo.Code.Effect.Functor qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Level qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Effect.Applicative.RawApplicative
d_RawApplicative_20 a0 a1 a2 = ()
data T_RawApplicative_20
  = C_RawApplicative'46'constructor_453 MAlonzo.Code.Effect.Functor.T_RawFunctor_24
                                        (() -> AgdaAny -> AgdaAny)
                                        (() -> () -> AgdaAny -> AgdaAny -> AgdaAny)
-- Effect.Applicative.RawApplicative.rawFunctor
d_rawFunctor_30 ::
  T_RawApplicative_20 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_30 v0
  = case coe v0 of
      C_RawApplicative'46'constructor_453 v1 v2 v3 -> coe v1
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.RawApplicative.pure
d_pure_32 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_pure_32 v0
  = case coe v0 of
      C_RawApplicative'46'constructor_453 v1 v2 v3 -> coe v2
      _                                            -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.RawApplicative._<*>_
d__'60''42''62'__34 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__34 v0
  = case coe v0 of
      C_RawApplicative'46'constructor_453 v1 v2 v3 -> coe v3
      _                                            -> MAlonzo.RTE.mazUnreachableError
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
d_mkRawApplicative_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> AgdaAny -> AgdaAny) ->
  (() -> () -> AgdaAny -> AgdaAny -> AgdaAny) -> T_RawApplicative_20
d_mkRawApplicative_94 ~v0 ~v1 ~v2 v3 v4
  = du_mkRawApplicative_94 v3 v4
du_mkRawApplicative_94 ::
  (() -> AgdaAny -> AgdaAny) ->
  (() -> () -> AgdaAny -> AgdaAny -> AgdaAny) -> T_RawApplicative_20
du_mkRawApplicative_94 v0 v1
  = coe
      C_RawApplicative'46'constructor_453
      (coe
         MAlonzo.Code.Effect.Functor.C_RawFunctor'46'constructor_241
         (coe
            (\ v2 v3 ->
               coe
                 MAlonzo.Code.Function.Base.du__'8728''8242'__216 (coe v1 v2 v3)
                 (coe v0 ()))))
      (coe (\ v2 -> coe v0 v2)) (coe (\ v2 v3 -> coe v1 v2 v3))
-- Effect.Applicative.RawApplicativeZero
d_RawApplicativeZero_120 a0 a1 a2 = ()
data T_RawApplicativeZero_120
  = C_RawApplicativeZero'46'constructor_8049 T_RawApplicative_20
                                             MAlonzo.Code.Effect.Empty.T_RawEmpty_16
-- Effect.Applicative.RawApplicativeZero.rawApplicative
d_rawApplicative_128 ::
  T_RawApplicativeZero_120 -> T_RawApplicative_20
d_rawApplicative_128 v0
  = case coe v0 of
      C_RawApplicativeZero'46'constructor_8049 v1 v2 -> coe v1
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.RawApplicativeZero.rawEmpty
d_rawEmpty_130 ::
  T_RawApplicativeZero_120 -> MAlonzo.Code.Effect.Empty.T_RawEmpty_16
d_rawEmpty_130 v0
  = case coe v0 of
      C_RawApplicativeZero'46'constructor_8049 v1 v2 -> coe v2
      _                                              -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.RawApplicativeZero._._*>_
d__'42''62'__134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__134 ~v0 ~v1 ~v2 v3 = du__'42''62'__134 v3
du__'42''62'__134 ::
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__134 v0 v1 v2 v3 v4
  = coe du__'42''62'__52 (coe d_rawApplicative_128 (coe v0)) v3 v4
-- Effect.Applicative.RawApplicativeZero._._<$_
d__'60''36'__136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__136 ~v0 ~v1 ~v2 v3 = du__'60''36'__136 v3
du__'60''36'__136 ::
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__136 v0
  = let v1 = d_rawApplicative_128 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Functor.du__'60''36'__32
           (coe d_rawFunctor_30 (coe v1)) v4 v5)
-- Effect.Applicative.RawApplicativeZero._._<$>_
d__'60''36''62'__138 ::
  T_RawApplicativeZero_120 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__138 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe d_rawFunctor_30 (coe d_rawApplicative_128 (coe v0)))
-- Effect.Applicative.RawApplicativeZero._._<&>_
d__'60''38''62'__140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__140 ~v0 ~v1 ~v2 v3 = du__'60''38''62'__140 v3
du__'60''38''62'__140 ::
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__140 v0
  = let v1 = d_rawApplicative_128 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe
           MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
           (coe d_rawFunctor_30 (coe v1)) v4 v5)
-- Effect.Applicative.RawApplicativeZero._._<*_
d__'60''42'__142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__142 ~v0 ~v1 ~v2 v3 = du__'60''42'__142 v3
du__'60''42'__142 ::
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__142 v0 v1 v2 v3 v4
  = coe du__'60''42'__46 (coe d_rawApplicative_128 (coe v0)) v3 v4
-- Effect.Applicative.RawApplicativeZero._._<*>_
d__'60''42''62'__144 ::
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__144 v0
  = coe d__'60''42''62'__34 (coe d_rawApplicative_128 (coe v0))
-- Effect.Applicative.RawApplicativeZero._._<⊛_
d__'60''8859'__146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__146 ~v0 ~v1 ~v2 v3 = du__'60''8859'__146 v3
du__'60''8859'__146 ::
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__146 v0 v1 v2
  = coe du__'60''8859'__72 (coe d_rawApplicative_128 (coe v0))
-- Effect.Applicative.RawApplicativeZero._._⊗_
d__'8855'__148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__148 ~v0 ~v1 ~v2 v3 = du__'8855'__148 v3
du__'8855'__148 ::
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__148 v0 v1 v2
  = coe du__'8855'__76 (coe d_rawApplicative_128 (coe v0))
-- Effect.Applicative.RawApplicativeZero._._⊛_
d__'8859'__150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__150 ~v0 ~v1 ~v2 v3 = du__'8859'__150 v3
du__'8859'__150 ::
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__150 v0 v1 v2
  = coe du__'8859'__70 (coe d_rawApplicative_128 (coe v0))
-- Effect.Applicative.RawApplicativeZero._._⊛>_
d__'8859''62'__152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__152 ~v0 ~v1 ~v2 v3 = du__'8859''62'__152 v3
du__'8859''62'__152 ::
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__152 v0 v1 v2
  = coe du__'8859''62'__74 (coe d_rawApplicative_128 (coe v0))
-- Effect.Applicative.RawApplicativeZero._.ignore
d_ignore_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawApplicativeZero_120 -> () -> AgdaAny -> AgdaAny
d_ignore_154 ~v0 ~v1 ~v2 v3 = du_ignore_154 v3
du_ignore_154 ::
  T_RawApplicativeZero_120 -> () -> AgdaAny -> AgdaAny
du_ignore_154 v0
  = let v1 = d_rawApplicative_128 (coe v0) in
    coe
      (\ v2 ->
         coe
           MAlonzo.Code.Effect.Functor.du_ignore_40
           (coe d_rawFunctor_30 (coe v1)))
-- Effect.Applicative.RawApplicativeZero._.pure
d_pure_156 :: T_RawApplicativeZero_120 -> () -> AgdaAny -> AgdaAny
d_pure_156 v0 = coe d_pure_32 (coe d_rawApplicative_128 (coe v0))
-- Effect.Applicative.RawApplicativeZero._.rawFunctor
d_rawFunctor_158 ::
  T_RawApplicativeZero_120 ->
  MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_158 v0
  = coe d_rawFunctor_30 (coe d_rawApplicative_128 (coe v0))
-- Effect.Applicative.RawApplicativeZero._.return
d_return_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawApplicativeZero_120 -> () -> AgdaAny -> AgdaAny
d_return_160 ~v0 ~v1 ~v2 v3 = du_return_160 v3
du_return_160 ::
  T_RawApplicativeZero_120 -> () -> AgdaAny -> AgdaAny
du_return_160 v0 v1
  = coe du_return_68 (coe d_rawApplicative_128 (coe v0))
-- Effect.Applicative.RawApplicativeZero._.zip
d_zip_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_162 ~v0 ~v1 ~v2 v3 = du_zip_162 v3
du_zip_162 ::
  T_RawApplicativeZero_120 ->
  () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_162 v0 v1 v2
  = coe du_zip_66 (coe d_rawApplicative_128 (coe v0))
-- Effect.Applicative.RawApplicativeZero._.zipWith
d_zipWith_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawApplicativeZero_120 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_164 ~v0 ~v1 ~v2 v3 = du_zipWith_164 v3
du_zipWith_164 ::
  T_RawApplicativeZero_120 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_164 v0 v1 v2 v3 v4 v5 v6
  = coe du_zipWith_58 (coe d_rawApplicative_128 (coe v0)) v4 v5 v6
-- Effect.Applicative.RawApplicativeZero._.empty
d_empty_168 :: T_RawApplicativeZero_120 -> () -> AgdaAny
d_empty_168 v0
  = coe
      MAlonzo.Code.Effect.Empty.d_empty_22 (coe d_rawEmpty_130 (coe v0))
-- Effect.Applicative.RawApplicativeZero._.∅
d_'8709'_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawApplicativeZero_120 -> () -> AgdaAny
d_'8709'_170 ~v0 ~v1 ~v2 v3 = du_'8709'_170 v3
du_'8709'_170 :: T_RawApplicativeZero_120 -> () -> AgdaAny
du_'8709'_170 v0 v1
  = coe
      MAlonzo.Code.Effect.Empty.du_'8709'_24
      (coe d_rawEmpty_130 (coe v0))
-- Effect.Applicative.RawApplicativeZero.guard
d_guard_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawApplicativeZero_120 -> Bool -> AgdaAny
d_guard_172 ~v0 ~v1 ~v2 v3 v4 = du_guard_172 v3 v4
du_guard_172 :: T_RawApplicativeZero_120 -> Bool -> AgdaAny
du_guard_172 v0 v1
  = if coe v1
      then coe
             d_pure_32 (d_rawApplicative_128 (coe v0)) erased
             (coe
                MAlonzo.Code.Level.C_lift_20
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      else coe
             MAlonzo.Code.Effect.Empty.d_empty_22 (d_rawEmpty_130 (coe v0))
             erased
-- Effect.Applicative.RawAlternative
d_RawAlternative_180 a0 a1 a2 = ()
data T_RawAlternative_180
  = C_RawAlternative'46'constructor_9897 T_RawApplicativeZero_120
                                         MAlonzo.Code.Effect.Choice.T_RawChoice_16
-- Effect.Applicative.RawAlternative.rawApplicativeZero
d_rawApplicativeZero_188 ::
  T_RawAlternative_180 -> T_RawApplicativeZero_120
d_rawApplicativeZero_188 v0
  = case coe v0 of
      C_RawAlternative'46'constructor_9897 v1 v2 -> coe v1
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.RawAlternative.rawChoice
d_rawChoice_190 ::
  T_RawAlternative_180 -> MAlonzo.Code.Effect.Choice.T_RawChoice_16
d_rawChoice_190 v0
  = case coe v0 of
      C_RawAlternative'46'constructor_9897 v1 v2 -> coe v2
      _                                          -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.RawAlternative._._*>_
d__'42''62'__194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__194 ~v0 ~v1 ~v2 v3 = du__'42''62'__194 v3
du__'42''62'__194 ::
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__194 v0
  = let v1 = d_rawApplicativeZero_188 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe du__'42''62'__52 (coe d_rawApplicative_128 (coe v1)) v4 v5)
-- Effect.Applicative.RawAlternative._._<$_
d__'60''36'__196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__196 ~v0 ~v1 ~v2 v3 = du__'60''36'__196 v3
du__'60''36'__196 ::
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__196 v0
  = let v1 = d_rawApplicativeZero_188 (coe v0) in
    coe
      (let v2 = d_rawApplicative_128 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Functor.du__'60''36'__32
              (coe d_rawFunctor_30 (coe v2)) v5 v6))
-- Effect.Applicative.RawAlternative._._<$>_
d__'60''36''62'__198 ::
  T_RawAlternative_180 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__198 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe
         d_rawFunctor_30
         (coe d_rawApplicative_128 (coe d_rawApplicativeZero_188 (coe v0))))
-- Effect.Applicative.RawAlternative._._<&>_
d__'60''38''62'__200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_180 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__200 ~v0 ~v1 ~v2 v3 = du__'60''38''62'__200 v3
du__'60''38''62'__200 ::
  T_RawAlternative_180 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__200 v0
  = let v1 = d_rawApplicativeZero_188 (coe v0) in
    coe
      (let v2 = d_rawApplicative_128 (coe v1) in
       coe
         (\ v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
              (coe d_rawFunctor_30 (coe v2)) v5 v6))
-- Effect.Applicative.RawAlternative._._<*_
d__'60''42'__202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__202 ~v0 ~v1 ~v2 v3 = du__'60''42'__202 v3
du__'60''42'__202 ::
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__202 v0
  = let v1 = d_rawApplicativeZero_188 (coe v0) in
    coe
      (\ v2 v3 v4 v5 ->
         coe du__'60''42'__46 (coe d_rawApplicative_128 (coe v1)) v4 v5)
-- Effect.Applicative.RawAlternative._._<*>_
d__'60''42''62'__204 ::
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__204 v0
  = coe
      d__'60''42''62'__34
      (coe d_rawApplicative_128 (coe d_rawApplicativeZero_188 (coe v0)))
-- Effect.Applicative.RawAlternative._._<⊛_
d__'60''8859'__206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__206 ~v0 ~v1 ~v2 v3 = du__'60''8859'__206 v3
du__'60''8859'__206 ::
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__206 v0
  = let v1 = d_rawApplicativeZero_188 (coe v0) in
    coe
      (\ v2 v3 ->
         coe du__'60''8859'__72 (coe d_rawApplicative_128 (coe v1)))
-- Effect.Applicative.RawAlternative._._⊗_
d__'8855'__208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__208 ~v0 ~v1 ~v2 v3 = du__'8855'__208 v3
du__'8855'__208 ::
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__208 v0
  = let v1 = d_rawApplicativeZero_188 (coe v0) in
    coe
      (\ v2 v3 -> coe du__'8855'__76 (coe d_rawApplicative_128 (coe v1)))
-- Effect.Applicative.RawAlternative._._⊛_
d__'8859'__210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__210 ~v0 ~v1 ~v2 v3 = du__'8859'__210 v3
du__'8859'__210 ::
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__210 v0
  = let v1 = d_rawApplicativeZero_188 (coe v0) in
    coe
      (\ v2 v3 -> coe du__'8859'__70 (coe d_rawApplicative_128 (coe v1)))
-- Effect.Applicative.RawAlternative._._⊛>_
d__'8859''62'__212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__212 ~v0 ~v1 ~v2 v3 = du__'8859''62'__212 v3
du__'8859''62'__212 ::
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__212 v0
  = let v1 = d_rawApplicativeZero_188 (coe v0) in
    coe
      (\ v2 v3 ->
         coe du__'8859''62'__74 (coe d_rawApplicative_128 (coe v1)))
-- Effect.Applicative.RawAlternative._.empty
d_empty_214 :: T_RawAlternative_180 -> () -> AgdaAny
d_empty_214 v0
  = coe
      MAlonzo.Code.Effect.Empty.d_empty_22
      (coe d_rawEmpty_130 (coe d_rawApplicativeZero_188 (coe v0)))
-- Effect.Applicative.RawAlternative._.guard
d_guard_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawAlternative_180 -> Bool -> AgdaAny
d_guard_216 ~v0 ~v1 ~v2 v3 = du_guard_216 v3
du_guard_216 :: T_RawAlternative_180 -> Bool -> AgdaAny
du_guard_216 v0
  = coe du_guard_172 (coe d_rawApplicativeZero_188 (coe v0))
-- Effect.Applicative.RawAlternative._.ignore
d_ignore_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawAlternative_180 -> () -> AgdaAny -> AgdaAny
d_ignore_218 ~v0 ~v1 ~v2 v3 = du_ignore_218 v3
du_ignore_218 :: T_RawAlternative_180 -> () -> AgdaAny -> AgdaAny
du_ignore_218 v0
  = let v1 = d_rawApplicativeZero_188 (coe v0) in
    coe
      (let v2 = d_rawApplicative_128 (coe v1) in
       coe
         (\ v3 ->
            coe
              MAlonzo.Code.Effect.Functor.du_ignore_40
              (coe d_rawFunctor_30 (coe v2))))
-- Effect.Applicative.RawAlternative._.pure
d_pure_220 :: T_RawAlternative_180 -> () -> AgdaAny -> AgdaAny
d_pure_220 v0
  = coe
      d_pure_32
      (coe d_rawApplicative_128 (coe d_rawApplicativeZero_188 (coe v0)))
-- Effect.Applicative.RawAlternative._.rawApplicative
d_rawApplicative_222 :: T_RawAlternative_180 -> T_RawApplicative_20
d_rawApplicative_222 v0
  = coe d_rawApplicative_128 (coe d_rawApplicativeZero_188 (coe v0))
-- Effect.Applicative.RawAlternative._.rawEmpty
d_rawEmpty_224 ::
  T_RawAlternative_180 -> MAlonzo.Code.Effect.Empty.T_RawEmpty_16
d_rawEmpty_224 v0
  = coe d_rawEmpty_130 (coe d_rawApplicativeZero_188 (coe v0))
-- Effect.Applicative.RawAlternative._.rawFunctor
d_rawFunctor_226 ::
  T_RawAlternative_180 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_226 v0
  = coe
      d_rawFunctor_30
      (coe d_rawApplicative_128 (coe d_rawApplicativeZero_188 (coe v0)))
-- Effect.Applicative.RawAlternative._.return
d_return_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawAlternative_180 -> () -> AgdaAny -> AgdaAny
d_return_228 ~v0 ~v1 ~v2 v3 = du_return_228 v3
du_return_228 :: T_RawAlternative_180 -> () -> AgdaAny -> AgdaAny
du_return_228 v0
  = let v1 = d_rawApplicativeZero_188 (coe v0) in
    coe (\ v2 -> coe du_return_68 (coe d_rawApplicative_128 (coe v1)))
-- Effect.Applicative.RawAlternative._.zip
d_zip_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_230 ~v0 ~v1 ~v2 v3 = du_zip_230 v3
du_zip_230 ::
  T_RawAlternative_180 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_230 v0
  = let v1 = d_rawApplicativeZero_188 (coe v0) in
    coe (\ v2 v3 -> coe du_zip_66 (coe d_rawApplicative_128 (coe v1)))
-- Effect.Applicative.RawAlternative._.zipWith
d_zipWith_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_180 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_232 ~v0 ~v1 ~v2 v3 = du_zipWith_232 v3
du_zipWith_232 ::
  T_RawAlternative_180 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_232 v0
  = let v1 = d_rawApplicativeZero_188 (coe v0) in
    coe
      (\ v2 v3 v4 v5 v6 v7 ->
         coe du_zipWith_58 (coe d_rawApplicative_128 (coe v1)) v5 v6 v7)
-- Effect.Applicative.RawAlternative._.∅
d_'8709'_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) -> T_RawAlternative_180 -> () -> AgdaAny
d_'8709'_234 ~v0 ~v1 ~v2 v3 = du_'8709'_234 v3
du_'8709'_234 :: T_RawAlternative_180 -> () -> AgdaAny
du_'8709'_234 v0
  = let v1 = d_rawApplicativeZero_188 (coe v0) in
    coe
      (\ v2 ->
         coe
           MAlonzo.Code.Effect.Empty.du_'8709'_24
           (coe d_rawEmpty_130 (coe v1)))
-- Effect.Applicative.RawAlternative._._<|>_
d__'60''124''62'__238 ::
  T_RawAlternative_180 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''124''62'__238 v0
  = coe
      MAlonzo.Code.Effect.Choice.d__'60''124''62'__22
      (coe d_rawChoice_190 (coe v0))
-- Effect.Applicative.RawAlternative._._∣_
d__'8739'__240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  T_RawAlternative_180 -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8739'__240 ~v0 ~v1 ~v2 v3 = du__'8739'__240 v3
du__'8739'__240 ::
  T_RawAlternative_180 -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8739'__240 v0 v1
  = coe
      MAlonzo.Code.Effect.Choice.du__'8739'__24
      (coe d_rawChoice_190 (coe v0))
-- Effect.Applicative.Morphism
d_Morphism_254 a0 a1 a2 a3 a4 a5 = ()
newtype T_Morphism_254
  = C_Morphism'46'constructor_14129 MAlonzo.Code.Effect.Functor.T_Morphism_58
-- Effect.Applicative.A₁._*>_
d__'42''62'__266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__266 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'42''62'__266 v4
du__'42''62'__266 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__266 v0 v1 v2 v3 v4
  = coe du__'42''62'__52 (coe v0) v3 v4
-- Effect.Applicative.A₁._<$_
d__'60''36'__268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__268 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'60''36'__268 v4
du__'60''36'__268 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__268 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''36'__32
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.A₁._<$>_
d__'60''36''62'__270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__270 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du__'60''36''62'__270 v4
du__'60''36''62'__270 ::
  T_RawApplicative_20 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62'__270 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.A₁._<&>_
d__'60''38''62'__272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__272 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du__'60''38''62'__272 v4
du__'60''38''62'__272 ::
  T_RawApplicative_20 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__272 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.A₁._<*_
d__'60''42'__274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__274 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'60''42'__274 v4
du__'60''42'__274 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__274 v0 v1 v2 v3 v4
  = coe du__'60''42'__46 (coe v0) v3 v4
-- Effect.Applicative.A₁._<*>_
d__'60''42''62'__276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__276 ~v0 ~v1 ~v2 ~v3 v4 ~v5
  = du__'60''42''62'__276 v4
du__'60''42''62'__276 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42''62'__276 v0 = coe d__'60''42''62'__34 (coe v0)
-- Effect.Applicative.A₁._<⊛_
d__'60''8859'__278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__278 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'60''8859'__278 v4
du__'60''8859'__278 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__278 v0 v1 v2 = coe du__'60''8859'__72 (coe v0)
-- Effect.Applicative.A₁._⊗_
d__'8855'__280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__280 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8855'__280 v4
du__'8855'__280 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__280 v0 v1 v2 = coe du__'8855'__76 (coe v0)
-- Effect.Applicative.A₁._⊛_
d__'8859'__282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__282 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8859'__282 v4
du__'8859'__282 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__282 v0 v1 v2 = coe du__'8859'__70 (coe v0)
-- Effect.Applicative.A₁._⊛>_
d__'8859''62'__284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__284 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du__'8859''62'__284 v4
du__'8859''62'__284 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__284 v0 v1 v2 = coe du__'8859''62'__74 (coe v0)
-- Effect.Applicative.A₁.ignore
d_ignore_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_ignore_286 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_ignore_286 v4
du_ignore_286 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_ignore_286 v0 v1
  = coe
      MAlonzo.Code.Effect.Functor.du_ignore_40
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.A₁.pure
d_pure_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_pure_288 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_pure_288 v4
du_pure_288 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_pure_288 v0 = coe d_pure_32 (coe v0)
-- Effect.Applicative.A₁.rawFunctor
d_rawFunctor_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_290 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_rawFunctor_290 v4
du_rawFunctor_290 ::
  T_RawApplicative_20 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
du_rawFunctor_290 v0 = coe d_rawFunctor_30 (coe v0)
-- Effect.Applicative.A₁.return
d_return_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_return_292 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_return_292 v4
du_return_292 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_return_292 v0 v1 = coe du_return_68 (coe v0)
-- Effect.Applicative.A₁.zip
d_zip_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_294 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_zip_294 v4
du_zip_294 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_294 v0 v1 v2 = coe du_zip_66 (coe v0)
-- Effect.Applicative.A₁.zipWith
d_zipWith_296 ::
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
d_zipWith_296 ~v0 ~v1 ~v2 ~v3 v4 ~v5 = du_zipWith_296 v4
du_zipWith_296 ::
  T_RawApplicative_20 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_296 v0 v1 v2 v3 v4 v5 v6
  = coe du_zipWith_58 (coe v0) v4 v5 v6
-- Effect.Applicative.A₂._*>_
d__'42''62'__300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__300 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'42''62'__300 v5
du__'42''62'__300 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__300 v0 v1 v2 v3 v4
  = coe du__'42''62'__52 (coe v0) v3 v4
-- Effect.Applicative.A₂._<$_
d__'60''36'__302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__302 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'60''36'__302 v5
du__'60''36'__302 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__302 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''36'__32
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.A₂._<$>_
d__'60''36''62'__304 ::
  T_RawApplicative_20 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__304 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.A₂._<&>_
d__'60''38''62'__306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__306 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du__'60''38''62'__306 v5
du__'60''38''62'__306 ::
  T_RawApplicative_20 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__306 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.A₂._<*_
d__'60''42'__308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__308 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'60''42'__308 v5
du__'60''42'__308 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__308 v0 v1 v2 v3 v4
  = coe du__'60''42'__46 (coe v0) v3 v4
-- Effect.Applicative.A₂._<*>_
d__'60''42''62'__310 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__310 v0 = coe d__'60''42''62'__34 (coe v0)
-- Effect.Applicative.A₂._<⊛_
d__'60''8859'__312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__312 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'60''8859'__312 v5
du__'60''8859'__312 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__312 v0 v1 v2 = coe du__'60''8859'__72 (coe v0)
-- Effect.Applicative.A₂._⊗_
d__'8855'__314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__314 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'8855'__314 v5
du__'8855'__314 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__314 v0 v1 v2 = coe du__'8855'__76 (coe v0)
-- Effect.Applicative.A₂._⊛_
d__'8859'__316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__316 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'8859'__316 v5
du__'8859'__316 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__316 v0 v1 v2 = coe du__'8859'__70 (coe v0)
-- Effect.Applicative.A₂._⊛>_
d__'8859''62'__318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__318 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du__'8859''62'__318 v5
du__'8859''62'__318 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__318 v0 v1 v2 = coe du__'8859''62'__74 (coe v0)
-- Effect.Applicative.A₂.ignore
d_ignore_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_ignore_320 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_ignore_320 v5
du_ignore_320 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_ignore_320 v0 v1
  = coe
      MAlonzo.Code.Effect.Functor.du_ignore_40
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.A₂.pure
d_pure_322 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_pure_322 v0 = coe d_pure_32 (coe v0)
-- Effect.Applicative.A₂.rawFunctor
d_rawFunctor_324 ::
  T_RawApplicative_20 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_324 v0 = coe d_rawFunctor_30 (coe v0)
-- Effect.Applicative.A₂.return
d_return_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
d_return_326 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_return_326 v5
du_return_326 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_return_326 v0 v1 = coe du_return_68 (coe v0)
-- Effect.Applicative.A₂.zip
d_zip_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_328 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_zip_328 v5
du_zip_328 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_328 v0 v1 v2 = coe du_zip_66 (coe v0)
-- Effect.Applicative.A₂.zipWith
d_zipWith_330 ::
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
d_zipWith_330 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_zipWith_330 v5
du_zipWith_330 ::
  T_RawApplicative_20 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_330 v0 v1 v2 v3 v4 v5 v6
  = coe du_zipWith_58 (coe v0) v4 v5 v6
-- Effect.Applicative.Morphism.A₁._*>_
d__'42''62'__352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__352 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du__'42''62'__352 v4
du__'42''62'__352 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__352 v0 v1 v2 v3 v4
  = coe du__'42''62'__52 (coe v0) v3 v4
-- Effect.Applicative.Morphism.A₁._<$_
d__'60''36'__354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__354 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du__'60''36'__354 v4
du__'60''36'__354 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__354 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''36'__32
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.Morphism.A₁._<$>_
d__'60''36''62'__356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__356 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du__'60''36''62'__356 v4
du__'60''36''62'__356 ::
  T_RawApplicative_20 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62'__356 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.Morphism.A₁._<&>_
d__'60''38''62'__358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__358 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du__'60''38''62'__358 v4
du__'60''38''62'__358 ::
  T_RawApplicative_20 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__358 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.Morphism.A₁._<*_
d__'60''42'__360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__360 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du__'60''42'__360 v4
du__'60''42'__360 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__360 v0 v1 v2 v3 v4
  = coe du__'60''42'__46 (coe v0) v3 v4
-- Effect.Applicative.Morphism.A₁._<*>_
d__'60''42''62'__362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__362 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du__'60''42''62'__362 v4
du__'60''42''62'__362 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42''62'__362 v0 = coe d__'60''42''62'__34 (coe v0)
-- Effect.Applicative.Morphism.A₁._<⊛_
d__'60''8859'__364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__364 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du__'60''8859'__364 v4
du__'60''8859'__364 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__364 v0 v1 v2 = coe du__'60''8859'__72 (coe v0)
-- Effect.Applicative.Morphism.A₁._⊗_
d__'8855'__366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__366 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du__'8855'__366 v4
du__'8855'__366 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__366 v0 v1 v2 = coe du__'8855'__76 (coe v0)
-- Effect.Applicative.Morphism.A₁._⊛_
d__'8859'__368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__368 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du__'8859'__368 v4
du__'8859'__368 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__368 v0 v1 v2 = coe du__'8859'__70 (coe v0)
-- Effect.Applicative.Morphism.A₁._⊛>_
d__'8859''62'__370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__370 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6
  = du__'8859''62'__370 v4
du__'8859''62'__370 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__370 v0 v1 v2 = coe du__'8859''62'__74 (coe v0)
-- Effect.Applicative.Morphism.A₁.ignore
d_ignore_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> T_Morphism_254 -> () -> AgdaAny -> AgdaAny
d_ignore_372 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_ignore_372 v4
du_ignore_372 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_ignore_372 v0 v1
  = coe
      MAlonzo.Code.Effect.Functor.du_ignore_40
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.Morphism.A₁.pure
d_pure_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> T_Morphism_254 -> () -> AgdaAny -> AgdaAny
d_pure_374 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_pure_374 v4
du_pure_374 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_pure_374 v0 = coe d_pure_32 (coe v0)
-- Effect.Applicative.Morphism.A₁.rawFunctor
d_rawFunctor_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_376 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_rawFunctor_376 v4
du_rawFunctor_376 ::
  T_RawApplicative_20 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
du_rawFunctor_376 v0 = coe d_rawFunctor_30 (coe v0)
-- Effect.Applicative.Morphism.A₁.return
d_return_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> T_Morphism_254 -> () -> AgdaAny -> AgdaAny
d_return_378 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_return_378 v4
du_return_378 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_return_378 v0 v1 = coe du_return_68 (coe v0)
-- Effect.Applicative.Morphism.A₁.zip
d_zip_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_380 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_zip_380 v4
du_zip_380 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_380 v0 v1 v2 = coe du_zip_66 (coe v0)
-- Effect.Applicative.Morphism.A₁.zipWith
d_zipWith_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_382 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 = du_zipWith_382 v4
du_zipWith_382 ::
  T_RawApplicative_20 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_382 v0 v1 v2 v3 v4 v5 v6
  = coe du_zipWith_58 (coe v0) v4 v5 v6
-- Effect.Applicative.Morphism.A₂._*>_
d__'42''62'__386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'42''62'__386 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du__'42''62'__386 v5
du__'42''62'__386 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'42''62'__386 v0 v1 v2 v3 v4
  = coe du__'42''62'__52 (coe v0) v3 v4
-- Effect.Applicative.Morphism.A₂._<$_
d__'60''36'__388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36'__388 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du__'60''36'__388 v5
du__'60''36'__388 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''36'__388 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''36'__32
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.Morphism.A₂._<$>_
d__'60''36''62'__390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'60''36''62'__390 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du__'60''36''62'__390 v5
du__'60''36''62'__390 ::
  T_RawApplicative_20 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'60''36''62'__390 v0
  = coe
      MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.Morphism.A₂._<&>_
d__'60''38''62'__392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'60''38''62'__392 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du__'60''38''62'__392 v5
du__'60''38''62'__392 ::
  T_RawApplicative_20 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
du__'60''38''62'__392 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
      (coe d_rawFunctor_30 (coe v0)) v3 v4
-- Effect.Applicative.Morphism.A₂._<*_
d__'60''42'__394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42'__394 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du__'60''42'__394 v5
du__'60''42'__394 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42'__394 v0 v1 v2 v3 v4
  = coe du__'60''42'__46 (coe v0) v3 v4
-- Effect.Applicative.Morphism.A₂._<*>_
d__'60''42''62'__396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''42''62'__396 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du__'60''42''62'__396 v5
du__'60''42''62'__396 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''42''62'__396 v0 = coe d__'60''42''62'__34 (coe v0)
-- Effect.Applicative.Morphism.A₂._<⊛_
d__'60''8859'__398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''8859'__398 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du__'60''8859'__398 v5
du__'60''8859'__398 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'60''8859'__398 v0 v1 v2 = coe du__'60''8859'__72 (coe v0)
-- Effect.Applicative.Morphism.A₂._⊗_
d__'8855'__400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8855'__400 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du__'8855'__400 v5
du__'8855'__400 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8855'__400 v0 v1 v2 = coe du__'8855'__76 (coe v0)
-- Effect.Applicative.Morphism.A₂._⊛_
d__'8859'__402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859'__402 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du__'8859'__402 v5
du__'8859'__402 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859'__402 v0 v1 v2 = coe du__'8859'__70 (coe v0)
-- Effect.Applicative.Morphism.A₂._⊛>_
d__'8859''62'__404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'8859''62'__404 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6
  = du__'8859''62'__404 v5
du__'8859''62'__404 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'8859''62'__404 v0 v1 v2 = coe du__'8859''62'__74 (coe v0)
-- Effect.Applicative.Morphism.A₂.ignore
d_ignore_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> T_Morphism_254 -> () -> AgdaAny -> AgdaAny
d_ignore_406 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_ignore_406 v5
du_ignore_406 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_ignore_406 v0 v1
  = coe
      MAlonzo.Code.Effect.Functor.du_ignore_40
      (coe d_rawFunctor_30 (coe v0))
-- Effect.Applicative.Morphism.A₂.pure
d_pure_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> T_Morphism_254 -> () -> AgdaAny -> AgdaAny
d_pure_408 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_pure_408 v5
du_pure_408 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_pure_408 v0 = coe d_pure_32 (coe v0)
-- Effect.Applicative.Morphism.A₂.rawFunctor
d_rawFunctor_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_410 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_rawFunctor_410 v5
du_rawFunctor_410 ::
  T_RawApplicative_20 -> MAlonzo.Code.Effect.Functor.T_RawFunctor_24
du_rawFunctor_410 v0 = coe d_rawFunctor_30 (coe v0)
-- Effect.Applicative.Morphism.A₂.return
d_return_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 -> T_Morphism_254 -> () -> AgdaAny -> AgdaAny
d_return_412 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_return_412 v5
du_return_412 :: T_RawApplicative_20 -> () -> AgdaAny -> AgdaAny
du_return_412 v0 v1 = coe du_return_68 (coe v0)
-- Effect.Applicative.Morphism.A₂.zip
d_zip_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d_zip_414 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_zip_414 v5
du_zip_414 ::
  T_RawApplicative_20 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du_zip_414 v0 v1 v2 = coe du_zip_66 (coe v0)
-- Effect.Applicative.Morphism.A₂.zipWith
d_zipWith_416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_zipWith_416 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 = du_zipWith_416 v5
du_zipWith_416 ::
  T_RawApplicative_20 ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_zipWith_416 v0 v1 v2 v3 v4 v5 v6
  = coe du_zipWith_58 (coe v0) v4 v5 v6
-- Effect.Applicative.Morphism.functorMorphism
d_functorMorphism_418 ::
  T_Morphism_254 -> MAlonzo.Code.Effect.Functor.T_Morphism_58
d_functorMorphism_418 v0
  = case coe v0 of
      C_Morphism'46'constructor_14129 v1 -> coe v1
      _                                  -> MAlonzo.RTE.mazUnreachableError
-- Effect.Applicative.Morphism._.op
d_op_422 :: T_Morphism_254 -> () -> AgdaAny -> AgdaAny
d_op_422 v0
  = coe
      MAlonzo.Code.Effect.Functor.d_op_76
      (coe d_functorMorphism_418 (coe v0))
-- Effect.Applicative.Morphism._.op-<$>
d_op'45''60''36''62'_424 ::
  T_Morphism_254 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45''60''36''62'_424 = erased
-- Effect.Applicative.Morphism.op-pure
d_op'45'pure_428 ::
  T_Morphism_254 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45'pure_428 = erased
-- Effect.Applicative.Morphism.op-<*>
d_op'45''60''42''62'_434 ::
  T_Morphism_254 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45''60''42''62'_434 = erased
-- Effect.Applicative.Morphism.op-⊛
d_op'45''8859'_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  (() -> ()) ->
  T_RawApplicative_20 ->
  T_RawApplicative_20 ->
  T_Morphism_254 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_op'45''8859'_436 = erased
