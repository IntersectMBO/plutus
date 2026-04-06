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

module MAlonzo.Code.Relation.Binary.Construct.On where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Relation.Binary.Construct.On._.implies
d_implies_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_implies_38 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_implies_38 v4 v9 v10 v11
du_implies_38 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_implies_38 v0 v1 v2 v3
  = coe
      v1
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292 v0
         (\ v4 v5 -> v4) v2 v3)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v4 v5 -> v5) v0 v2 v3)
-- Relation.Binary.Construct.On._.reflexive
d_reflexive_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_reflexive_44 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_reflexive_44 v4 v7 v8
du_reflexive_44 ::
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_reflexive_44 v0 v1 v2
  = coe
      v1
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292 v0
         (\ v3 v4 -> v3) v2 v2)
-- Relation.Binary.Construct.On._.irreflexive
d_irreflexive_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irreflexive_52 = erased
-- Relation.Binary.Construct.On._.symmetric
d_symmetric_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_symmetric_58 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8 v9
  = du_symmetric_58 v4 v7 v8 v9
du_symmetric_58 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_symmetric_58 v0 v1 v2 v3
  = coe
      v1
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292 v0
         (\ v4 v5 -> v4) v2 v3)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v4 v5 -> v5) v0 v2 v3)
-- Relation.Binary.Construct.On._.transitive
d_transitive_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_transitive_64 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8 v9 v10
  = du_transitive_64 v4 v7 v8 v9 v10
du_transitive_64 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_transitive_64 v0 v1 v2 v3 v4
  = coe
      v1
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292 v0
         (\ v5 v6 -> v5) v2 v3)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v5 v6 -> v6) v0 v2 v3)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v5 v6 -> v6) v0 v3 v4)
-- Relation.Binary.Construct.On._.antisymmetric
d_antisymmetric_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisymmetric_72 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_antisymmetric_72 v4 v9 v10 v11
du_antisymmetric_72 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisymmetric_72 v0 v1 v2 v3
  = coe
      v1
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292 v0
         (\ v4 v5 -> v4) v2 v3)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v4 v5 -> v5) v0 v2 v3)
-- Relation.Binary.Construct.On._.asymmetric
d_asymmetric_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asymmetric_78 = erased
-- Relation.Binary.Construct.On._.respects
d_respects_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_respects_86 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_respects_86 v4 v9 v10 v11
du_respects_86 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_respects_86 v0 v1 v2 v3
  = coe
      v1
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292 v0
         (\ v4 v5 -> v4) v2 v3)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v4 v5 -> v5) v0 v2 v3)
-- Relation.Binary.Construct.On._.respects₂
d_respects'8322'_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_respects'8322'_94 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9
  = du_respects'8322'_94 v4 v9
du_respects'8322'_94 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_respects'8322'_94 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                (\ v4 v5 v6 ->
                   coe
                     v2
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292 v0
                        (\ v7 v8 -> v7) v4 v5)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292 v0
                        (\ v7 v8 -> v7) v5 v6)
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v7 v8 -> v8) v0 v5 v6)))
             (coe
                (\ v4 v5 v6 ->
                   coe
                     v3
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v7 v8 -> v8) v0 v5 v4)
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292 v0
                        (\ v7 v8 -> v7) v5 v6)
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v7 v8 -> v8) v0 v5 v6)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.On._.decidable
d_decidable_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decidable_102 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8 v9
  = du_decidable_102 v4 v7 v8 v9
du_decidable_102 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_decidable_102 v0 v1 v2 v3 = coe v1 (coe v0 v2) (coe v0 v3)
-- Relation.Binary.Construct.On._.total
d_total_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_112 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8 v9
  = du_total_112 v4 v7 v8 v9
du_total_112 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_total_112 v0 v1 v2 v3 = coe v1 (coe v0 v2) (coe v0 v3)
-- Relation.Binary.Construct.On._.trichotomous
d_trichotomous_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_trichotomous_124 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
  = du_trichotomous_124 v4 v9 v10 v11
du_trichotomous_124 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_trichotomous_124 v0 v1 v2 v3 = coe v1 (coe v0 v2) (coe v0 v3)
-- Relation.Binary.Construct.On._.accessible
d_accessible_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_accessible_136 = erased
-- Relation.Binary.Construct.On._.wellFounded
d_wellFounded_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  AgdaAny -> MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_wellFounded_144 = erased
-- Relation.Binary.Construct.On._.isEquivalence
d_isEquivalence_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_164 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_isEquivalence_164 v5 v7
du_isEquivalence_164 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_164 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_46
      (coe
         du_reflexive_44 (coe v0)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_refl_36 (coe v1)))
      (coe
         du_symmetric_58 (coe v0)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_38 (coe v1)))
      (coe
         du_transitive_64 (coe v0)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_40 (coe v1)))
-- Relation.Binary.Construct.On._.isDecEquivalence
d_isDecEquivalence_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_isDecEquivalence_184 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_isDecEquivalence_184 v5 v7
du_isDecEquivalence_184 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_isDecEquivalence_184 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_70
      (coe
         du_isEquivalence_164 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
            (coe v1)))
      (coe
         du_decidable_102 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__56 (coe v1)))
-- Relation.Binary.Construct.On._.isPreorder
d_isPreorder_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_isPreorder_226 v6 v9
du_isPreorder_226 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_isPreorder_226 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         du_isEquivalence_164 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe v1)))
      (coe
         du_implies_38 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88 (coe v1)))
      (coe
         du_transitive_64 (coe v0)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_90 (coe v1)))
-- Relation.Binary.Construct.On._.isPartialOrder
d_isPartialOrder_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_isPartialOrder_268 v6 v9
du_isPartialOrder_268 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_isPartialOrder_268 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         du_isPreorder_226 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
      (coe
         du_antisymmetric_72 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_antisym_258 (coe v1)))
-- Relation.Binary.Construct.On._.isDecPartialOrder
d_isDecPartialOrder_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
d_isDecPartialOrder_314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_isDecPartialOrder_314 v6 v9
du_isDecPartialOrder_314 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
du_isDecPartialOrder_314 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_364
      (coe
         du_isPartialOrder_268 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_310
            (coe v1)))
      (coe
         du_decidable_102 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__312 (coe v1)))
      (coe
         du_decidable_102 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__314
            (coe v1)))
-- Relation.Binary.Construct.On._.isStrictPartialOrder
d_isStrictPartialOrder_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_isStrictPartialOrder_374 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_isStrictPartialOrder_374 v6 v9
du_isStrictPartialOrder_374 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
du_isStrictPartialOrder_374 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_412
      (coe
         du_isEquivalence_164 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
            (coe v1)))
      (coe
         du_transitive_64 (coe v0)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_386 (coe v1)))
      (coe
         du_respects'8322'_94 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
            (coe v1)))
-- Relation.Binary.Construct.On._.isTotalOrder
d_isTotalOrder_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_isTotalOrder_410 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_isTotalOrder_410 v6 v9
du_isTotalOrder_410 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
du_isTotalOrder_410 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_540
      (coe
         du_isPartialOrder_268 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
            (coe v1)))
      (coe
         du_total_112 (coe v0)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_total_498 (coe v1)))
-- Relation.Binary.Construct.On._.isDecTotalOrder
d_isDecTotalOrder_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_isDecTotalOrder_462 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_isDecTotalOrder_462 v6 v9
du_isDecTotalOrder_462 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
du_isDecTotalOrder_462 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_618
      (coe
         du_isTotalOrder_410 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_556
            (coe v1)))
      (coe
         du_decidable_102 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__558 (coe v1)))
      (coe
         du_decidable_102 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__560
            (coe v1)))
-- Relation.Binary.Construct.On._.isStrictTotalOrder
d_isStrictTotalOrder_530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_isStrictTotalOrder_530 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_isStrictTotalOrder_530 v6 v9
du_isStrictTotalOrder_530 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
du_isStrictTotalOrder_530 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_680
      (coe
         du_isStrictPartialOrder_374 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
            (coe v1)))
      (coe
         du_trichotomous_124 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_634 (coe v1)))
-- Relation.Binary.Construct.On.preorder
d_preorder_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_preorder_586 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_preorder_586 v5 v6
du_preorder_586 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_preorder_586 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_232
      (coe
         du_isPreorder_226 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0)))
-- Relation.Binary.Construct.On.setoid
d_setoid_594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_594 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_setoid_594 v4 v5
du_setoid_594 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_594 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      (coe
         du_isEquivalence_164 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v0)))
-- Relation.Binary.Construct.On.decSetoid
d_decSetoid_602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_decSetoid_602 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_decSetoid_602 v4 v5
du_decSetoid_602 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
du_decSetoid_602 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_134
      (coe
         du_isDecEquivalence_184 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_106
            (coe v0)))
-- Relation.Binary.Construct.On.poset
d_poset_610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_610 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_poset_610 v5 v6
du_poset_610 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_610 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      (coe
         du_isPartialOrder_268 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
            (coe v0)))
-- Relation.Binary.Construct.On.decPoset
d_decPoset_618 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecPoset_596 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecPoset_596
d_decPoset_618 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_decPoset_618 v5 v6
du_decPoset_618 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecPoset_596 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecPoset_596
du_decPoset_618 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_752
      (coe
         du_isDecPartialOrder_314 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecPartialOrder_618
            (coe v0)))
-- Relation.Binary.Construct.On.strictPartialOrder
d_strictPartialOrder_626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
d_strictPartialOrder_626 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_strictPartialOrder_626 v5 v6
du_strictPartialOrder_626 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
du_strictPartialOrder_626 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_842
      (coe
         du_isStrictPartialOrder_374 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_782
            (coe v0)))
-- Relation.Binary.Construct.On.totalOrder
d_totalOrder_634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
d_totalOrder_634 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_totalOrder_634 v5 v6
du_totalOrder_634 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
du_totalOrder_634 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1090
      (coe
         du_isTotalOrder_410 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008 (coe v0)))
-- Relation.Binary.Construct.On.decTotalOrder
d_decTotalOrder_642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
d_decTotalOrder_642 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_decTotalOrder_642 v5 v6
du_decTotalOrder_642 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
du_decTotalOrder_642 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1272
      (coe
         du_isDecTotalOrder_462 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_1120
            (coe v0)))
-- Relation.Binary.Construct.On.strictTotalOrder
d_strictTotalOrder_650 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
d_strictTotalOrder_650 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_strictTotalOrder_650 v5 v6
du_strictTotalOrder_650 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
du_strictTotalOrder_650 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1386
      (coe
         du_isStrictTotalOrder_530 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1302
            (coe v0)))
