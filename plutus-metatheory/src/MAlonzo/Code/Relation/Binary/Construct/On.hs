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

module MAlonzo.Code.Relation.Binary.Construct.On where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Induction.WellFounded qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_164 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_isEquivalence_164 v5 v7
du_isEquivalence_164 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_164 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (coe
         du_reflexive_44 (coe v0)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_refl_34 (coe v1)))
      (coe
         du_symmetric_58 (coe v0)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_36 (coe v1)))
      (coe
         du_transitive_64 (coe v0)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_38 (coe v1)))
-- Relation.Binary.Construct.On._.isDecEquivalence
d_isDecEquivalence_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_isDecEquivalence_184 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7
  = du_isDecEquivalence_184 v5 v7
du_isDecEquivalence_184 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_isDecEquivalence_184 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecEquivalence'46'constructor_3083
      (coe
         du_isEquivalence_164 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
            (coe v1)))
      (coe
         du_decidable_102 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__52 (coe v1)))
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
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_isPreorder_226 v6 v9
du_isPreorder_226 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_isPreorder_226 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         du_isEquivalence_164 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe v1)))
      (coe
         du_implies_38 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82 (coe v1)))
      (coe
         du_transitive_64 (coe v0)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_84 (coe v1)))
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
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_isPartialOrder_268 v6 v9
du_isPartialOrder_268 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_isPartialOrder_268 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_9853
      (coe
         du_isPreorder_226 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v1)))
      (coe
         du_antisymmetric_72 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_antisym_184 (coe v1)))
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
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
d_isDecPartialOrder_314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_isDecPartialOrder_314 v6 v9
du_isDecPartialOrder_314 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
du_isDecPartialOrder_314 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecPartialOrder'46'constructor_11683
      (coe
         du_isPartialOrder_268 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_234
            (coe v1)))
      (coe
         du_decidable_102 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__236 (coe v1)))
      (coe
         du_decidable_102 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__238
            (coe v1)))
-- Relation.Binary.Construct.On._.isStrictPartialOrder
d_isStrictPartialOrder_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_isStrictPartialOrder_372 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_isStrictPartialOrder_372 v6 v9
du_isStrictPartialOrder_372 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_isStrictPartialOrder_372 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_14045
      (coe
         du_isEquivalence_164 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
            (coe v1)))
      (coe
         du_transitive_64 (coe v0)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_306 (coe v1)))
      (coe
         du_respects'8322'_94 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
            (coe v1)))
-- Relation.Binary.Construct.On._.isTotalOrder
d_isTotalOrder_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
d_isTotalOrder_408 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_isTotalOrder_408 v6 v9
du_isTotalOrder_408 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
du_isTotalOrder_408 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalOrder'46'constructor_20555
      (coe
         du_isPartialOrder_268 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
            (coe v1)))
      (coe
         du_total_112 (coe v0)
         (coe MAlonzo.Code.Relation.Binary.Structures.d_total_414 (coe v1)))
-- Relation.Binary.Construct.On._.isDecTotalOrder
d_isDecTotalOrder_460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
d_isDecTotalOrder_460 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_isDecTotalOrder_460 v6 v9
du_isDecTotalOrder_460 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
du_isDecTotalOrder_460 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecTotalOrder'46'constructor_22695
      (coe
         du_isTotalOrder_408 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_470
            (coe v1)))
      (coe
         du_decidable_102 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__472 (coe v1)))
      (coe
         du_decidable_102 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__474
            (coe v1)))
-- Relation.Binary.Construct.On._.isStrictTotalOrder
d_isStrictTotalOrder_526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_isStrictTotalOrder_526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_isStrictTotalOrder_526 v6 v9
du_isStrictTotalOrder_526 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
du_isStrictTotalOrder_526 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_24953
      (coe
         du_isStrictPartialOrder_372 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
            (coe v1)))
      (coe
         du_trichotomous_124 (coe v0)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_544 (coe v1)))
-- Relation.Binary.Construct.On.preorder
d_preorder_582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_preorder_582 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_preorder_582 v5 v6
du_preorder_582 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_preorder_582 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2267
      (coe
         du_isPreorder_226 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0)))
-- Relation.Binary.Construct.On.setoid
d_setoid_590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_590 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_setoid_590 v4 v5
du_setoid_590 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_590 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_733
      (coe
         du_isEquivalence_164 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
-- Relation.Binary.Construct.On.decSetoid
d_decSetoid_598 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_decSetoid_598 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_decSetoid_598 v4 v5
du_decSetoid_598 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
du_decSetoid_598 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecSetoid'46'constructor_1389
      (coe
         du_isDecEquivalence_184 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_100
            (coe v0)))
-- Relation.Binary.Construct.On.poset
d_poset_606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_606 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_poset_606 v5 v6
du_poset_606 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_606 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_6389
      (coe
         du_isPartialOrder_268 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
            (coe v0)))
-- Relation.Binary.Construct.On.decPoset
d_decPoset_614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecPoset_406 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecPoset_406
d_decPoset_614 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_decPoset_614 v5 v6
du_decPoset_614 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecPoset_406 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecPoset_406
du_decPoset_614 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecPoset'46'constructor_8213
      (coe
         du_isDecPartialOrder_314 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecPartialOrder_428
            (coe v0)))
-- Relation.Binary.Construct.On.strictPartialOrder
d_strictPartialOrder_622 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_strictPartialOrder_622 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_strictPartialOrder_622 v5 v6
du_strictPartialOrder_622 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
du_strictPartialOrder_622 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictPartialOrder'46'constructor_11097
      (coe
         du_isStrictPartialOrder_372 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
            (coe v0)))
-- Relation.Binary.Construct.On.totalOrder
d_totalOrder_630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
d_totalOrder_630 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_totalOrder_630 v5 v6
du_totalOrder_630 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
du_totalOrder_630 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalOrder'46'constructor_15747
      (coe
         du_isTotalOrder_408 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0)))
-- Relation.Binary.Construct.On.decTotalOrder
d_decTotalOrder_638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
d_decTotalOrder_638 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_decTotalOrder_638 v5 v6
du_decTotalOrder_638 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
du_decTotalOrder_638 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecTotalOrder'46'constructor_17849
      (coe
         du_isDecTotalOrder_460 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_888
            (coe v0)))
-- Relation.Binary.Construct.On.strictTotalOrder
d_strictTotalOrder_646 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
d_strictTotalOrder_646 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_strictTotalOrder_646 v5 v6
du_strictTotalOrder_646 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
du_strictTotalOrder_646 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictTotalOrder'46'constructor_21059
      (coe
         du_isStrictTotalOrder_526 (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
            (coe v0)))
