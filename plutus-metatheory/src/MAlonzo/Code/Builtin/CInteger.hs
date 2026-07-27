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

module MAlonzo.Code.Builtin.CInteger where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Builtin.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Maybe.Effectful
import qualified MAlonzo.Code.Effect.Applicative
import qualified MAlonzo.Code.Effect.Functor
import qualified MAlonzo.Code.Effect.Monad
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Builtin.CInteger._._*>_
d__'42''62'__6 ::
  () -> () -> Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d__'42''62'__6
  = let v0 = coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'42''62'__52
           (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)) v3 v4)
-- Builtin.CInteger._._<$_
d__'60''36'__8 ::
  () -> () -> AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d__'60''36'__8
  = let v0 = coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34 in
    coe
      (let v1 = MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0) in
       coe
         (\ v2 v3 v4 v5 ->
            coe
              MAlonzo.Code.Effect.Functor.du__'60''36'__32
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v1)) v4
              v5))
-- Builtin.CInteger._._<$>_
d__'60''36''62'__10 ::
  () -> () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d__'60''36''62'__10 ~v0 = du__'60''36''62'__10
du__'60''36''62'__10 ::
  () -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
du__'60''36''62'__10 v0 v1
  = coe MAlonzo.Code.Data.Maybe.Base.du_map_64 v1
-- Builtin.CInteger._._<&>_
d__'60''38''62'__12 ::
  () -> () -> Maybe AgdaAny -> (AgdaAny -> AgdaAny) -> Maybe AgdaAny
d__'60''38''62'__12
  = let v0 = coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34 in
    coe
      (let v1 = MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0) in
       coe
         (\ v2 v3 v4 v5 ->
            coe
              MAlonzo.Code.Effect.Functor.du__'60''38''62'__38
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v1)) v4
              v5))
-- Builtin.CInteger._._<*_
d__'60''42'__14 ::
  () -> () -> Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d__'60''42'__14
  = let v0 = coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'60''42'__46
           (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)) v3 v4)
-- Builtin.CInteger._._<*>_
d__'60''42''62'__16 ::
  () ->
  () -> Maybe (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d__'60''42''62'__16 ~v0 ~v1 = du__'60''42''62'__16
du__'60''42''62'__16 ::
  Maybe (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
du__'60''42''62'__16
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe_32
      (coe MAlonzo.Code.Data.Maybe.Base.du_map_64)
      (let v0 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
       coe (coe (\ v1 -> v0)))
-- Builtin.CInteger._._<=<_
d__'60''61''60'__18 ::
  () ->
  () ->
  () ->
  (AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe AgdaAny) -> AgdaAny -> Maybe AgdaAny
d__'60''61''60'__18 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Effect.Monad.du__'60''61''60'__88
      (coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34) v3 v4
-- Builtin.CInteger._._<⊛_
d__'60''8859'__20 ::
  () -> () -> Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d__'60''8859'__20
  = let v0 = coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34 in
    coe
      (\ v1 v2 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'60''8859'__72
           (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)))
-- Builtin.CInteger._._=<<_
d__'61''60''60'__22 ::
  () ->
  () -> (AgdaAny -> Maybe AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d__'61''60''60'__22 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Effect.Monad.du__'61''60''60'__72
      (coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34) v2 v3
-- Builtin.CInteger._._>=>_
d__'62''61''62'__24 ::
  () ->
  () ->
  () ->
  (AgdaAny -> Maybe AgdaAny) ->
  (AgdaAny -> Maybe AgdaAny) -> AgdaAny -> Maybe AgdaAny
d__'62''61''62'__24 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Effect.Monad.du__'62''61''62'__80
      (coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34) v3 v4 v5
-- Builtin.CInteger._._>>_
d__'62''62'__26 ::
  () -> () -> Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d__'62''62'__26 v0 v1
  = coe
      MAlonzo.Code.Effect.Monad.du__'62''62'__70
      (coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34)
-- Builtin.CInteger._._>>=_
d__'62''62''61'__28 ::
  () ->
  () -> Maybe AgdaAny -> (AgdaAny -> Maybe AgdaAny) -> Maybe AgdaAny
d__'62''62''61'__28 ~v0 = du__'62''62''61'__28
du__'62''62''61'__28 ::
  () -> Maybe AgdaAny -> (AgdaAny -> Maybe AgdaAny) -> Maybe AgdaAny
du__'62''62''61'__28 v0 v1 v2
  = coe MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72 v1 v2
-- Builtin.CInteger._._⊗_
d__'8855'__30 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8855'__30
  = let v0 = coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34 in
    coe
      (\ v1 v2 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8855'__76
           (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)))
-- Builtin.CInteger._._⊛_
d__'8859'__32 ::
  () ->
  () -> Maybe (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> Maybe AgdaAny
d__'8859'__32
  = let v0 = coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34 in
    coe
      (\ v1 v2 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8859'__70
           (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)))
-- Builtin.CInteger._._⊛>_
d__'8859''62'__34 ::
  () -> () -> Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d__'8859''62'__34
  = let v0 = coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34 in
    coe
      (\ v1 v2 ->
         coe
           MAlonzo.Code.Effect.Applicative.du__'8859''62'__74
           (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)))
-- Builtin.CInteger._.Kleisli
d_Kleisli_36 :: () -> () -> ()
d_Kleisli_36 = erased
-- Builtin.CInteger._.ignore
d_ignore_38 ::
  () -> Maybe AgdaAny -> Maybe MAlonzo.Code.Level.T_Lift_8
d_ignore_38
  = let v0 = coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34 in
    coe
      (let v1 = MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0) in
       coe
         (\ v2 ->
            coe
              MAlonzo.Code.Effect.Functor.du_ignore_40
              (coe MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v1))))
-- Builtin.CInteger._.pure
d_pure_40 :: () -> AgdaAny -> Maybe AgdaAny
d_pure_40 ~v0 = du_pure_40
du_pure_40 :: AgdaAny -> Maybe AgdaAny
du_pure_40 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
-- Builtin.CInteger._.rawApplicative
d_rawApplicative_42 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_rawApplicative_42
  = coe MAlonzo.Code.Data.Maybe.Effectful.du_applicative_24
-- Builtin.CInteger._.rawFunctor
d_rawFunctor_44 :: MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_rawFunctor_44
  = coe MAlonzo.Code.Data.Maybe.Effectful.du_functor_22
-- Builtin.CInteger._.return
d_return_46 :: () -> AgdaAny -> Maybe AgdaAny
d_return_46
  = let v0 = coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34 in
    coe
      (\ v1 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_return_68
           (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)))
-- Builtin.CInteger._.unless
d_unless_48 ::
  Bool ->
  Maybe MAlonzo.Code.Level.T_Lift_8 ->
  Maybe MAlonzo.Code.Level.T_Lift_8
d_unless_48
  = coe
      MAlonzo.Code.Effect.Monad.du_unless_96
      (coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34)
-- Builtin.CInteger._.when
d_when_50 ::
  Bool ->
  Maybe MAlonzo.Code.Level.T_Lift_8 ->
  Maybe MAlonzo.Code.Level.T_Lift_8
d_when_50
  = coe
      MAlonzo.Code.Effect.Monad.du_when_90
      (coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34)
-- Builtin.CInteger._.zip
d_zip_52 ::
  () ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zip_52
  = let v0 = coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34 in
    coe
      (\ v1 v2 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_zip_66
           (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)))
-- Builtin.CInteger._.zipWith
d_zipWith_54 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d_zipWith_54
  = let v0 = coe MAlonzo.Code.Data.Maybe.Effectful.du_monad_34 in
    coe
      (\ v1 v2 v3 v4 v5 v6 ->
         coe
           MAlonzo.Code.Effect.Applicative.du_zipWith_58
           (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)) v4 v5
           v6)
-- Builtin.CInteger.minBound
d_minBound_56 :: Integer
d_minBound_56
  = coe
      MAlonzo.Code.Data.Integer.Base.d_'45'__260
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'94'__322 (coe (2 :: Integer))
         (coe (262143 :: Integer)))
-- Builtin.CInteger.maxBound
d_maxBound_58 :: Integer
d_maxBound_58
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'45'__302
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'94'__322 (coe (2 :: Integer))
         (coe (262143 :: Integer)))
      (coe (1 :: Integer))
-- Builtin.CInteger.CInteger
d_CInteger_60 = ()
data T_CInteger_60
  = C_cInt_64 Integer MAlonzo.Code.Data.Integer.Base.T__'8804'__26
              MAlonzo.Code.Data.Integer.Base.T__'8804'__26
-- Builtin.CInteger.add
d_add_66 :: T_CInteger_60 -> T_CInteger_60 -> Integer
d_add_66 v0 v1
  = case coe v0 of
      C_cInt_64 v2 v3 v4
        -> case coe v1 of
             C_cInt_64 v5 v6 v7
               -> coe
                    MAlonzo.Code.Data.Integer.Base.d__'43'__284 (coe v2) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.CInteger.subtract
d_subtract_72 :: T_CInteger_60 -> T_CInteger_60 -> Integer
d_subtract_72 v0 v1
  = case coe v0 of
      C_cInt_64 v2 v3 v4
        -> case coe v1 of
             C_cInt_64 v5 v6 v7
               -> coe
                    MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v2) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.CInteger.multiply
d_multiply_78 :: T_CInteger_60 -> T_CInteger_60 -> Integer
d_multiply_78 v0 v1
  = case coe v0 of
      C_cInt_64 v2 v3 v4
        -> case coe v1 of
             C_cInt_64 v5 v6 v7
               -> coe
                    MAlonzo.Code.Data.Integer.Base.d__'42'__316 (coe v2) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.CInteger.quot
d_quot_84 :: T_CInteger_60 -> T_CInteger_60 -> Maybe Integer
d_quot_84 v0 v1
  = case coe v0 of
      C_cInt_64 v2 v3 v4
        -> case coe v1 of
             C_cInt_64 v5 v6 v7
               -> let v8
                        = MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800
                            (coe v5) (coe (0 :: Integer)) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                         -> if coe v9
                              then coe
                                     seq (coe v10)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                              else coe
                                     seq (coe v10)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Builtin.Integer.Base.du_quot_12 (coe v2)
                                           (coe v5)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.CInteger.rem
d_rem_110 :: T_CInteger_60 -> T_CInteger_60 -> Maybe Integer
d_rem_110 v0 v1
  = case coe v0 of
      C_cInt_64 v2 v3 v4
        -> case coe v1 of
             C_cInt_64 v5 v6 v7
               -> let v8
                        = MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800
                            (coe v5) (coe (0 :: Integer)) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                         -> if coe v9
                              then coe
                                     seq (coe v10)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                              else coe
                                     seq (coe v10)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Builtin.Integer.Base.du_rem_24 (coe v2)
                                           (coe v5)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.CInteger.divMod
d_divMod_136 ::
  T_CInteger_60 ->
  T_CInteger_60 -> Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_divMod_136 v0 v1
  = case coe v0 of
      C_cInt_64 v2 v3 v4
        -> case coe v1 of
             C_cInt_64 v5 v6 v7
               -> let v8
                        = MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800
                            (coe v5) (coe (0 :: Integer)) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                         -> if coe v9
                              then coe
                                     seq (coe v10)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                              else coe
                                     seq (coe v10)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Builtin.Integer.Base.du_divMod_56 (coe v2)
                                           (coe v5)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.CInteger.div
d_div_162 :: T_CInteger_60 -> T_CInteger_60 -> Maybe Integer
d_div_162 v0 v1
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_map_64
      (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
      (d_divMod_136 (coe v0) (coe v1))
-- Builtin.CInteger.mod
d_mod_164 :: T_CInteger_60 -> T_CInteger_60 -> Maybe Integer
d_mod_164 v0 v1
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_map_64
      (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
      (d_divMod_136 (coe v0) (coe v1))
-- Builtin.CInteger.lessThan
d_lessThan_174 :: T_CInteger_60 -> T_CInteger_60 -> Bool
d_lessThan_174 v0 v1
  = case coe v0 of
      C_cInt_64 v2 v3 v4
        -> case coe v1 of
             C_cInt_64 v5 v6 v7
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                    (coe
                       MAlonzo.Code.Data.Integer.Properties.d__'60''63'__3190 (coe v2)
                       (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.CInteger.lessThanEquals
d_lessThanEquals_180 :: T_CInteger_60 -> T_CInteger_60 -> Bool
d_lessThanEquals_180 v0 v1
  = case coe v0 of
      C_cInt_64 v2 v3 v4
        -> case coe v1 of
             C_cInt_64 v5 v6 v7
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                    (coe
                       MAlonzo.Code.Data.Integer.Properties.d__'8804''63'__2880 (coe v2)
                       (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Builtin.CInteger.equals
d_equals_186 :: T_CInteger_60 -> T_CInteger_60 -> Bool
d_equals_186 v0 v1
  = case coe v0 of
      C_cInt_64 v2 v3 v4
        -> case coe v1 of
             C_cInt_64 v5 v6 v7
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                    (coe
                       MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800 (coe v2)
                       (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
