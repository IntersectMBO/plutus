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

module MAlonzo.Code.Relation.Nullary.Negation.Core where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Empty qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
  = coe MAlonzo.Code.Data.Empty.du_'8869''45'elim'45'irr_20
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
-- Relation.Nullary.Negation.Core.stable
d_stable_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  ((((AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
     MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
    AgdaAny) ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_stable_70 = erased
-- Relation.Nullary.Negation.Core.negated-stable
d_negated'45'stable_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (((AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
    MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_negated'45'stable_74 = erased
-- Relation.Nullary.Negation.Core.¬¬-map
d_'172''172''45'map_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  ((AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172''172''45'map_80 = erased
