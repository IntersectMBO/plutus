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

module MAlonzo.Code.Data.Maybe.Relation.Unary.Any where

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
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Nullary.Decidable
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Maybe.Relation.Unary.Any.Any
d_Any_18 a0 a1 a2 a3 a4 = ()
newtype T_Any_18 = C_just_30 AgdaAny
-- Data.Maybe.Relation.Unary.Any._.drop-just
d_drop'45'just_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> ()) -> AgdaAny -> T_Any_18 -> AgdaAny
d_drop'45'just_46 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_drop'45'just_46 v5
du_drop'45'just_46 :: T_Any_18 -> AgdaAny
du_drop'45'just_46 v0
  = case coe v0 of
      C_just_30 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Unary.Any._.just-equivalence
d_just'45'equivalence_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_just'45'equivalence_52 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_just'45'equivalence_52
du_just'45'equivalence_52 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_just'45'equivalence_52
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2474 (coe C_just_30)
      (coe du_drop'45'just_46)
-- Data.Maybe.Relation.Unary.Any._.map
d_map_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> T_Any_18 -> T_Any_18
d_map_58 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 = du_map_58 v6 v7 v8
du_map_58 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> T_Any_18 -> T_Any_18
du_map_58 v0 v1 v2
  = case coe v2 of
      C_just_30 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
               -> coe C_just_30 (coe v0 v5 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Unary.Any._.satisfied
d_satisfied_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  Maybe AgdaAny -> T_Any_18 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfied_66 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_satisfied_66 v4 v5
du_satisfied_66 ::
  Maybe AgdaAny -> T_Any_18 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfied_66 v0 v1
  = case coe v1 of
      C_just_30 v3
        -> case coe v0 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    MAlonzo.Code.Data.Product.Base.du_'45''44'__92 (coe v4) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Unary.Any._.zipWith
d_zipWith_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Any_18
d_zipWith_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_zipWith_90 v8 v9 v10
du_zipWith_90 ::
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Any_18
du_zipWith_90 v0 v1 v2
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
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Unary.Any._.unzipWith
d_unzipWith_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Maybe AgdaAny -> T_Any_18 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzipWith_98 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_unzipWith_98 v8 v9 v10
du_unzipWith_98 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Maybe AgdaAny -> T_Any_18 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzipWith_98 v0 v1 v2
  = case coe v2 of
      C_just_30 v4
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
               -> coe
                    MAlonzo.Code.Data.Product.Base.du_map_128 (coe C_just_30)
                    (coe (\ v6 -> coe C_just_30)) (coe v0 v5 v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Unary.Any._.zip
d_zip_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Any_18
d_zip_120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_zip_120 v6
du_zip_120 ::
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> T_Any_18
du_zip_120 v0 = coe du_zipWith_90 (coe (\ v1 v2 -> v2)) (coe v0)
-- Data.Maybe.Relation.Unary.Any._.unzip
d_unzip_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  Maybe AgdaAny -> T_Any_18 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzip_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_unzip_122 v6
du_unzip_122 ::
  Maybe AgdaAny -> T_Any_18 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzip_122 v0
  = coe du_unzipWith_98 (coe (\ v1 v2 -> v2)) (coe v0)
-- Data.Maybe.Relation.Unary.Any._.dec
d_dec_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_dec_136 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_dec_136 v4 v5
du_dec_136 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_dec_136 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.du_map_18
             (coe du_just'45'equivalence_52) (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
             (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Relation.Unary.Any._.irrelevant
d_irrelevant_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Maybe AgdaAny ->
  T_Any_18 ->
  T_Any_18 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_irrelevant_144 = erased
-- Data.Maybe.Relation.Unary.Any._.satisfiable
d_satisfiable_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_satisfiable_152 ~v0 ~v1 ~v2 ~v3 v4 = du_satisfiable_152 v4
du_satisfiable_152 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_satisfiable_152 v0
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16)
      (\ v1 v2 -> coe C_just_30 v2) (coe v0)
