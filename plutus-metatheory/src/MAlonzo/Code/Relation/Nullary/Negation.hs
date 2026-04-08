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

module MAlonzo.Code.Relation.Nullary.Negation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Effect.Monad
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Relation.Nullary.Negation.∃⟶¬∀¬
d_'8707''10230''172''8704''172'_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8707''10230''172''8704''172'_32 = erased
-- Relation.Nullary.Negation.∀⟶¬∃¬
d_'8704''10230''172''8707''172'_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8704''10230''172''8707''172'_38 = erased
-- Relation.Nullary.Negation.¬∃⟶∀¬
d_'172''8707''10230''8704''172'_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172''8707''10230''8704''172'_50 = erased
-- Relation.Nullary.Negation.∀¬⟶¬∃
d_'8704''172''10230''172''8707'_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8704''172''10230''172''8707'_56 = erased
-- Relation.Nullary.Negation.∃¬⟶¬∀
d_'8707''172''10230''172''8704'_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8707''172''10230''172''8704'_62 = erased
-- Relation.Nullary.Negation.¬¬-Monad
d_'172''172''45'Monad_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Effect.Monad.T_RawMonad_24
d_'172''172''45'Monad_64 ~v0 = du_'172''172''45'Monad_64
du_'172''172''45'Monad_64 ::
  MAlonzo.Code.Effect.Monad.T_RawMonad_24
du_'172''172''45'Monad_64
  = coe
      MAlonzo.Code.Effect.Monad.du_mkRawMonad_180
      (coe
         (\ v0 v1 ->
            coe
              MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44))
      erased
-- Relation.Nullary.Negation.¬¬-push
d_'172''172''45'push_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (((AgdaAny -> AgdaAny) ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172''172''45'push_70 = erased
-- Relation.Nullary.Negation.call/cc
d_call'47'cc_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ((AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_call'47'cc_80 = erased
-- Relation.Nullary.Negation.independence-of-premise
d_independence'45'of'45'premise_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_independence'45'of'45'premise_88 = erased
-- Relation.Nullary.Negation._.helper
d_helper_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_helper_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_helper_106 v6 v7 v8
du_helper_106 ::
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_helper_106 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then case coe v4 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v5
                      -> coe
                           MAlonzo.Code.Data.Product.Base.du_map'8322'_150 (\ v6 v7 v8 -> v7)
                           (coe v1 v5)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                       (coe
                          (\ v5 ->
                             coe
                               MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                               erased)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Nullary.Negation.independence-of-premise-⊎
d_independence'45'of'45'premise'45''8846'_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  (MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_independence'45'of'45'premise'45''8846'_112 = erased
-- Relation.Nullary.Negation._.helper
d_helper_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_helper_126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_helper_126 v6 v7
du_helper_126 ::
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_helper_126 v0 v1
  = case coe v1 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
        -> if coe v2
             then case coe v3 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v4
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.du_map_84 (\ v5 v6 -> v5)
                           (\ v5 v6 -> v5) (coe v0 v4)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe
                    seq (coe v3)
                    (coe
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                       (coe
                          (\ v4 ->
                             coe
                               MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                               erased)))
      _ -> MAlonzo.RTE.mazUnreachableError
