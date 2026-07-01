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

module MAlonzo.Code.Data.List.Effectful where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Effect.Applicative
import qualified MAlonzo.Code.Effect.Choice
import qualified MAlonzo.Code.Effect.Empty
import qualified MAlonzo.Code.Effect.Functor
import qualified MAlonzo.Code.Effect.Monad

-- Data.List.Effectful.functor
d_functor_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Functor.T_RawFunctor_24
d_functor_10 ~v0 = du_functor_10
du_functor_10 :: MAlonzo.Code.Effect.Functor.T_RawFunctor_24
du_functor_10
  = coe
      MAlonzo.Code.Effect.Functor.C_constructor_44
      (coe
         (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Data.List.Base.du_map_22 v2 v3))
-- Data.List.Effectful.applicative
d_applicative_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_applicative_12 ~v0 = du_applicative_12
du_applicative_12 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
du_applicative_12
  = coe
      MAlonzo.Code.Effect.Applicative.C_constructor_78
      (coe du_functor_10)
      (\ v0 v1 -> coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 v1)
      (coe
         (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Data.List.Base.du_ap_250 v2 v3))
-- Data.List.Effectful.empty
d_empty_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Empty.T_RawEmpty_16
d_empty_14 ~v0 = du_empty_14
du_empty_14 :: MAlonzo.Code.Effect.Empty.T_RawEmpty_16
du_empty_14
  = coe
      MAlonzo.Code.Effect.Empty.C_constructor_26
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Data.List.Effectful.choice
d_choice_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Choice.T_RawChoice_16
d_choice_16 ~v0 = du_choice_16
du_choice_16 :: MAlonzo.Code.Effect.Choice.T_RawChoice_16
du_choice_16
  = coe
      MAlonzo.Code.Effect.Choice.C_constructor_26
      (\ v0 v1 v2 ->
         coe MAlonzo.Code.Data.List.Base.du__'43''43'__32 v1 v2)
-- Data.List.Effectful.applicativeZero
d_applicativeZero_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicativeZero_122
d_applicativeZero_18 ~v0 = du_applicativeZero_18
du_applicativeZero_18 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicativeZero_122
du_applicativeZero_18
  = coe
      MAlonzo.Code.Effect.Applicative.C_constructor_176
      (coe du_applicative_12) (coe du_empty_14)
-- Data.List.Effectful.alternative
d_alternative_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Applicative.T_RawAlternative_184
d_alternative_20 ~v0 = du_alternative_20
du_alternative_20 ::
  MAlonzo.Code.Effect.Applicative.T_RawAlternative_184
du_alternative_20
  = coe
      MAlonzo.Code.Effect.Applicative.C_constructor_246
      (coe du_applicativeZero_18) (coe du_choice_16)
-- Data.List.Effectful.monad
d_monad_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24
d_monad_24 ~v0 = du_monad_24
du_monad_24 :: MAlonzo.Code.Effect.Monad.T_RawMonad_24
du_monad_24
  = coe
      MAlonzo.Code.Effect.Monad.C_constructor_98 (coe du_applicative_12)
      (coe
         (\ v0 v1 v2 v3 ->
            coe
              MAlonzo.Code.Data.List.Base.du_concatMap_246 (coe v3) (coe v2)))
-- Data.List.Effectful.join
d_join_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [[AgdaAny]] -> [AgdaAny]
d_join_26 ~v0 ~v1 = du_join_26
du_join_26 :: [[AgdaAny]] -> [AgdaAny]
du_join_26
  = coe MAlonzo.Code.Effect.Monad.du_join_160 (coe du_monad_24)
-- Data.List.Effectful.monadZero
d_monadZero_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Monad.T_RawMonadZero_208
d_monadZero_30 ~v0 = du_monadZero_30
du_monadZero_30 :: MAlonzo.Code.Effect.Monad.T_RawMonadZero_208
du_monadZero_30
  = coe
      MAlonzo.Code.Effect.Monad.C_constructor_280 (coe du_monad_24)
      (coe du_empty_14)
-- Data.List.Effectful.monadPlus
d_monadPlus_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Monad.T_RawMonadPlus_288
d_monadPlus_34 ~v0 = du_monadPlus_34
du_monadPlus_34 :: MAlonzo.Code.Effect.Monad.T_RawMonadPlus_288
du_monadPlus_34
  = coe
      MAlonzo.Code.Effect.Monad.C_constructor_370 (coe du_monadZero_30)
      (coe du_choice_16)
-- Data.List.Effectful.TraversableA.sequenceA
d_sequenceA_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  () -> [AgdaAny] -> AgdaAny
d_sequenceA_82 ~v0 ~v1 ~v2 v3 ~v4 v5 = du_sequenceA_82 v3 v5
du_sequenceA_82 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  [AgdaAny] -> AgdaAny
du_sequenceA_82 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Effect.Applicative.d_pure_32 v0 erased v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Effect.Applicative.d__'60''42''62'__34 v0 erased
             erased
             (coe
                MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
                (MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v0)) erased
                erased (coe MAlonzo.Code.Agda.Builtin.List.C__'8759'__22) v2)
             (coe du_sequenceA_82 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Effectful.TraversableA.mapA
d_mapA_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny
d_mapA_94 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 = du_mapA_94 v3 v7 v8
du_mapA_94 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  (AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny
du_mapA_94 v0 v1 v2
  = coe
      du_sequenceA_82 (coe v0)
      (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v1) (coe v2))
-- Data.List.Effectful.TraversableA.forA
d_forA_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> [AgdaAny] -> (AgdaAny -> AgdaAny) -> AgdaAny
d_forA_104 ~v0 ~v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 = du_forA_104 v3 v7 v8
du_forA_104 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  [AgdaAny] -> (AgdaAny -> AgdaAny) -> AgdaAny
du_forA_104 v0 v1 v2 = coe du_mapA_94 (coe v0) (coe v2) (coe v1)
-- Data.List.Effectful.TraversableM._.forA
d_forA_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> [AgdaAny] -> (AgdaAny -> AgdaAny) -> AgdaAny
d_forA_170 ~v0 ~v1 ~v2 v3 = du_forA_170 v3
du_forA_170 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> [AgdaAny] -> (AgdaAny -> AgdaAny) -> AgdaAny
du_forA_170 v0 v1 v2 v3 v4 v5
  = coe
      du_forA_104
      (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)) v4 v5
-- Data.List.Effectful.TraversableM._.mapA
d_mapA_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny
d_mapA_172 ~v0 ~v1 ~v2 v3 = du_mapA_172 v3
du_mapA_172 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> AgdaAny
du_mapA_172 v0 v1 v2 v3 v4 v5
  = coe
      du_mapA_94
      (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)) v4 v5
-- Data.List.Effectful.TraversableM._.sequenceA
d_sequenceA_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  () -> [AgdaAny] -> AgdaAny
d_sequenceA_174 ~v0 ~v1 ~v2 v3 = du_sequenceA_174 v3
du_sequenceA_174 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  () -> [AgdaAny] -> AgdaAny
du_sequenceA_174 v0 v1 v2
  = coe
      du_sequenceA_82
      (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)) v2
-- Data.List.Effectful.LMP._<$>_
d__'60''36''62'__184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
d__'60''36''62'__184 ~v0 ~v1 = du__'60''36''62'__184
du__'60''36''62'__184 ::
  () -> (AgdaAny -> AgdaAny) -> [AgdaAny] -> [AgdaAny]
du__'60''36''62'__184 v0 v1 v2
  = coe MAlonzo.Code.Data.List.Base.du_map_22 v1 v2
-- Data.List.Effectful.LMP._>>=_
d__'62''62''61'__204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> [AgdaAny] -> (AgdaAny -> [AgdaAny]) -> [AgdaAny]
d__'62''62''61'__204 ~v0 ~v1 ~v2 v3 v4
  = du__'62''62''61'__204 v3 v4
du__'62''62''61'__204 ::
  [AgdaAny] -> (AgdaAny -> [AgdaAny]) -> [AgdaAny]
du__'62''62''61'__204 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_concatMap_246 (coe v1) (coe v0)
-- Data.List.Effectful.LMP._∣_
d__'8739'__206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
d__'8739'__206 ~v0 = du__'8739'__206
du__'8739'__206 :: () -> [AgdaAny] -> [AgdaAny] -> [AgdaAny]
du__'8739'__206
  = let v0 = coe du_monadPlus_34 in
    coe
      (\ v1 ->
         coe
           MAlonzo.Code.Effect.Choice.du__'8739'__24
           (coe MAlonzo.Code.Effect.Monad.d_rawChoice_298 (coe v0)))
-- Data.List.Effectful.LMP._⊛_
d__'8859'__210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> [AgdaAny -> AgdaAny] -> [AgdaAny] -> [AgdaAny]
d__'8859'__210 ~v0 = du__'8859'__210
du__'8859'__210 ::
  () -> () -> [AgdaAny -> AgdaAny] -> [AgdaAny] -> [AgdaAny]
du__'8859'__210
  = let v0 = coe du_monadPlus_34 in
    coe
      (let v1 = MAlonzo.Code.Effect.Monad.d_rawMonadZero_296 (coe v0) in
       coe
         (let v2 = MAlonzo.Code.Effect.Monad.d_rawMonad_216 (coe v1) in
          coe
            (\ v3 v4 ->
               coe
                 MAlonzo.Code.Effect.Applicative.du__'8859'__70
                 (coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v2)))))
-- Data.List.Effectful.LMP.pure
d_pure_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> [AgdaAny]
d_pure_220 ~v0 = du_pure_220
du_pure_220 :: () -> AgdaAny -> [AgdaAny]
du_pure_220 v0 v1
  = coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 v1
-- Data.List.Effectful.LMP.∅
d_'8709'_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> [AgdaAny]
d_'8709'_248 ~v0 = du_'8709'_248
du_'8709'_248 :: () -> [AgdaAny]
du_'8709'_248
  = let v0 = coe du_monadPlus_34 in
    coe
      (let v1 = MAlonzo.Code.Effect.Monad.d_rawMonadZero_296 (coe v0) in
       coe
         (\ v2 ->
            coe
              MAlonzo.Code.Effect.Empty.du_'8709'_24
              (coe MAlonzo.Code.Effect.Monad.d_rawEmpty_218 (coe v1))))
-- Data.List.Effectful.MonadProperties.left-identity
d_left'45'identity_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> [AgdaAny]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'identity_262 = erased
-- Data.List.Effectful.MonadProperties.right-identity
d_right'45'identity_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_right'45'identity_274 = erased
-- Data.List.Effectful.MonadProperties.left-zero
d_left'45'zero_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'zero_290 = erased
-- Data.List.Effectful.MonadProperties.right-zero
d_right'45'zero_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_right'45'zero_302 = erased
-- Data.List.Effectful.MonadProperties.right-distributive
d_right'45'distributive_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> [AgdaAny]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_right'45'distributive_330 = erased
-- Data.List.Effectful.MonadProperties.associative
d_associative_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  [AgdaAny] ->
  (AgdaAny -> [AgdaAny]) ->
  (AgdaAny -> [AgdaAny]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_associative_362 = erased
-- Data.List.Effectful.MonadProperties.cong
d_cong_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> [AgdaAny]) ->
  (AgdaAny -> [AgdaAny]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_394 = erased
-- Data.List.Effectful.Applicative.MP.associative
d_associative_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  [AgdaAny] ->
  (AgdaAny -> [AgdaAny]) ->
  (AgdaAny -> [AgdaAny]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_associative_404 = erased
-- Data.List.Effectful.Applicative.MP.cong
d_cong_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> [AgdaAny]) ->
  (AgdaAny -> [AgdaAny]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong_406 = erased
-- Data.List.Effectful.Applicative.MP.left-identity
d_left'45'identity_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  (AgdaAny -> [AgdaAny]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'identity_408 = erased
-- Data.List.Effectful.Applicative.MP.left-zero
d_left'45'zero_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> [AgdaAny]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'zero_410 = erased
-- Data.List.Effectful.Applicative.MP.right-distributive
d_right'45'distributive_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> [AgdaAny]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_right'45'distributive_412 = erased
-- Data.List.Effectful.Applicative.MP.right-identity
d_right'45'identity_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_right'45'identity_414 = erased
-- Data.List.Effectful.Applicative.MP.right-zero
d_right'45'zero_416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_right'45'zero_416 = erased
-- Data.List.Effectful.Applicative.pam
d_pam_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> [AgdaAny] -> (AgdaAny -> AgdaAny) -> [AgdaAny]
d_pam_424 ~v0 ~v1 ~v2 v3 v4 = du_pam_424 v3 v4
du_pam_424 :: [AgdaAny] -> (AgdaAny -> AgdaAny) -> [AgdaAny]
du_pam_424 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_concatMap_246
      (coe
         (\ v2 ->
            coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1 v2)))
      (coe v0)
-- Data.List.Effectful.Applicative.left-zero
d_left'45'zero_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'zero_438 = erased
-- Data.List.Effectful.Applicative.right-zero
d_right'45'zero_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  [AgdaAny -> AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_right'45'zero_450 = erased
-- Data.List.Effectful.Applicative.unfold-<$>
d_unfold'45''60''36''62'_470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unfold'45''60''36''62'_470 = erased
-- Data.List.Effectful.Applicative.unfold-⊛
d_unfold'45''8859'_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  [AgdaAny -> AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unfold'45''8859'_486 = erased
-- Data.List.Effectful.Applicative.right-distributive
d_right'45'distributive_514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  [AgdaAny -> AgdaAny] ->
  [AgdaAny -> AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_right'45'distributive_514 = erased
-- Data.List.Effectful.Applicative.identity
d_identity_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_identity_536 = erased
-- Data.List.Effectful.Applicative.pam-lemma
d_pam'45'lemma_556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> [AgdaAny]) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pam'45'lemma_556 = erased
-- Data.List.Effectful.Applicative.composition
d_composition_584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  [AgdaAny -> AgdaAny] ->
  [AgdaAny -> AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_composition_584 = erased
-- Data.List.Effectful.Applicative.homomorphism
d_homomorphism_644 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_homomorphism_644 = erased
-- Data.List.Effectful.Applicative.interchange
d_interchange_662 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  [AgdaAny -> AgdaAny] ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_interchange_662 = erased
