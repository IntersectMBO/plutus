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

module MAlonzo.Code.Data.Maybe.Relation.Unary.All where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Maybe.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Effect.Applicative
import qualified MAlonzo.Code.Effect.Functor
import qualified MAlonzo.Code.Effect.Monad
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Nullary.Decidable
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Maybe.Relation.Unary.All.All
d_All_18 a0 a1 a2 a3 a4 = ()
data T_All_18 = C_just_30 AgdaAny | C_nothing_32
-- Data.Maybe.Relation.Unary.All._.drop-just
d_drop'45'just_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> AgdaAny -> T_All_18 -> AgdaAny
d_drop'45'just_48 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_drop'45'just_48 v5
du_drop'45'just_48 :: T_All_18 -> AgdaAny
du_drop'45'just_48 v0
  = case coe v0 of
      C_just_30 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Unary.All._.just-equivalence
d_just'45'equivalence_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_just'45'equivalence_54 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_just'45'equivalence_54
du_just'45'equivalence_54 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_just'45'equivalence_54
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2474 (coe C_just_30)
      (coe du_drop'45'just_48)
-- Data.Maybe.Relation.Unary.All._.map
d_map_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> T_All_18 -> T_All_18
d_map_60 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 = du_map_60 v6 v7 v8
du_map_60 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> T_All_18 -> T_All_18
du_map_60 v0 v1 v2
  = case coe v2 of
      C_just_30 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
               -> coe C_just_30 (coe v0 v5 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nothing_32 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Unary.All._.fromAny
d_fromAny_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  Maybe AgdaAny ->
  MAlonzo.Code.Data.Maybe.Relation.Unary.Any.T_Any_18 -> T_All_18
d_fromAny_68 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_fromAny_68 v5
du_fromAny_68 ::
  MAlonzo.Code.Data.Maybe.Relation.Unary.Any.T_Any_18 -> T_All_18
du_fromAny_68 v0
  = case coe v0 of
      MAlonzo.Code.Data.Maybe.Relation.Unary.Any.C_just_30 v2
        -> coe C_just_30 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Unary.All._.zipWith
d_zipWith_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_All_18
d_zipWith_92 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_zipWith_92 v8 v9 v10
du_zipWith_92 ::
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_All_18
du_zipWith_92 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> case coe v3 of
             C_just_30 v6
               -> case coe v1 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                      -> case coe v4 of
                           C_just_30 v9
                             -> coe
                                  C_just_30
                                  (coe
                                     v0 v7
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                        (coe v9)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             C_nothing_32 -> coe seq (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Unary.All._.unzipWith
d_unzipWith_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Maybe AgdaAny -> T_All_18 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzipWith_102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_unzipWith_102 v8 v9 v10
du_unzipWith_102 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Maybe AgdaAny -> T_All_18 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzipWith_102 v0 v1 v2
  = case coe v2 of
      C_just_30 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
               -> coe
                    MAlonzo.Code.Data.Product.Base.du_map_128 (coe C_just_30)
                    (coe (\ v6 -> coe C_just_30)) (coe v0 v5 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_nothing_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Unary.All._.zip
d_zip_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_All_18
d_zip_126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_zip_126 v6
du_zip_126 ::
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_All_18
du_zip_126 v0 = coe du_zipWith_92 (coe (\ v1 v2 -> v2)) (coe v0)
-- Data.Maybe.Relation.Unary.All._.unzip
d_unzip_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  Maybe AgdaAny -> T_All_18 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzip_128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_unzip_128 v6
du_unzip_128 ::
  Maybe AgdaAny -> T_All_18 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzip_128 v0
  = coe du_unzipWith_102 (coe (\ v1 v2 -> v2)) (coe v0)
-- Data.Maybe.Relation.Unary.All._.sequenceA
d_sequenceA_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  Maybe AgdaAny -> T_All_18 -> AgdaAny
d_sequenceA_182 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8
  = du_sequenceA_182 v6 v8
du_sequenceA_182 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  T_All_18 -> AgdaAny
du_sequenceA_182 v0 v1
  = case coe v1 of
      C_just_30 v3
        -> coe
             MAlonzo.Code.Effect.Functor.d__'60''36''62'__30
             (MAlonzo.Code.Effect.Applicative.d_rawFunctor_30 (coe v0)) erased
             erased (coe C_just_30) v3
      C_nothing_32
        -> coe MAlonzo.Code.Effect.Applicative.d_pure_32 v0 erased v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Unary.All._.mapA
d_mapA_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> T_All_18 -> AgdaAny
d_mapA_190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 v10
  = du_mapA_190 v6 v9 v10
du_mapA_190 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> T_All_18 -> AgdaAny
du_mapA_190 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe du_sequenceA_182 (coe v0)) (coe du_map_60 (coe v1) (coe v2))
-- Data.Maybe.Relation.Unary.All._.forA
d_forA_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  Maybe AgdaAny ->
  T_All_18 -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
d_forA_200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 v10 v11
  = du_forA_200 v6 v9 v10 v11
du_forA_200 ::
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20 ->
  Maybe AgdaAny ->
  T_All_18 -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
du_forA_200 v0 v1 v2 v3 = coe du_mapA_190 v0 v3 v1 v2
-- Data.Maybe.Relation.Unary.All._.App
d_App_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
d_App_224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_App_224 v6
du_App_224 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Effect.Applicative.T_RawApplicative_20
du_App_224 v0
  = coe MAlonzo.Code.Effect.Monad.d_rawApplicative_32 (coe v0)
-- Data.Maybe.Relation.Unary.All._.sequenceM
d_sequenceM_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  Maybe AgdaAny -> T_All_18 -> AgdaAny
d_sequenceM_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7
  = du_sequenceM_226 v6
du_sequenceM_226 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 -> T_All_18 -> AgdaAny
du_sequenceM_226 v0
  = coe du_sequenceA_182 (coe du_App_224 (coe v0))
-- Data.Maybe.Relation.Unary.All._.mapM
d_mapM_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> T_All_18 -> AgdaAny
d_mapM_232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 = du_mapM_232 v6
du_mapM_232 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> T_All_18 -> AgdaAny
du_mapM_232 v0 = coe du_mapA_190 (coe du_App_224 (coe v0))
-- Data.Maybe.Relation.Unary.All._.forM
d_forM_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (() -> ()) ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  Maybe AgdaAny ->
  T_All_18 -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
d_forM_240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_forM_240 v6 v9
du_forM_240 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24 ->
  Maybe AgdaAny ->
  T_All_18 -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny
du_forM_240 v0 v1
  = coe du_forA_200 (coe du_App_224 (coe v0)) (coe v1)
-- Data.Maybe.Relation.Unary.All._.dec
d_dec_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_dec_254 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_dec_254 v4 v5
du_dec_254 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_dec_254 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.du_map_18
             (coe du_just'45'equivalence_54) (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe C_nothing_32))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Unary.All._.universal
d_universal_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> T_All_18
d_universal_262 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_universal_262 v4 v5
du_universal_262 ::
  (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> T_All_18
du_universal_262 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe C_just_30 (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe C_nothing_32
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Unary.All._.irrelevant
d_irrelevant_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Maybe AgdaAny ->
  T_All_18 ->
  T_All_18 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irrelevant_270 = erased
-- Data.Maybe.Relation.Unary.All._.satisfiable
d_satisfiable_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfiable_280 ~v0 ~v1 ~v2 ~v3 = du_satisfiable_280
du_satisfiable_280 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfiable_280
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (coe C_nothing_32)
