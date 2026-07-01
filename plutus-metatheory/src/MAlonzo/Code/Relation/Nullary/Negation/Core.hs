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

module MAlonzo.Code.Relation.Nullary.Negation.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base

-- Relation.Nullary.Negation.Core.¬_
d_'172'__24 :: MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_'172'__24 = erased
-- Relation.Nullary.Negation.Core.DoubleNegation
d_DoubleNegation_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_DoubleNegation_28 = erased
-- Relation.Nullary.Negation.Core.Stable
d_Stable_32 :: MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_Stable_32 = erased
-- Relation.Nullary.Negation.Core._¬-⊎_
d__'172''45''8846'__36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d__'172''45''8846'__36 = erased
-- Relation.Nullary.Negation.Core.contradiction-irr
d_contradiction'45'irr_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_contradiction'45'irr_38 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_contradiction'45'irr_38
du_contradiction'45'irr_38 :: AgdaAny
du_contradiction'45'irr_38
  = coe MAlonzo.Code.Data.Empty.du_'8869''45'elim'45'irr_18
-- Relation.Nullary.Negation.Core.contradiction
d_contradiction_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_contradiction_44 ~v0 ~v1 ~v2 ~v3 ~v4 = du_contradiction_44
du_contradiction_44 ::
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
du_contradiction_44 v0 = coe du_contradiction'45'irr_38
-- Relation.Nullary.Negation.Core.contradiction₂
d_contradiction'8322'_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny
d_contradiction'8322'_48 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8
  = du_contradiction'8322'_48 v6
du_contradiction'8322'_48 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_contradiction'8322'_48 v0
  = coe seq (coe v0) (coe du_contradiction_44 erased)
-- Relation.Nullary.Negation.Core.contraposition
d_contraposition_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_contraposition_62 = erased
-- Relation.Nullary.Negation.Core.contra-diagonal
d_contra'45'diagonal_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_contra'45'diagonal_70 = erased
-- Relation.Nullary.Negation.Core.stable
d_stable_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ((((AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
     MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
    AgdaAny) ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stable_76 = erased
-- Relation.Nullary.Negation.Core.negated-stable
d_negated'45'stable_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (((AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_negated'45'stable_80 = erased
-- Relation.Nullary.Negation.Core.¬¬-map
d_'172''172''45'map_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  ((AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172''172''45'map_86 = erased
