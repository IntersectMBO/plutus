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

module MAlonzo.Code.Data.List.Relation.Binary.Lex.Strict where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.List.Relation.Binary.Lex qualified
import MAlonzo.Code.Data.List.Relation.Binary.Lex.Core qualified
import MAlonzo.Code.Data.List.Relation.Binary.Pointwise qualified
import MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base qualified
import MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.List.Relation.Binary.Lex.Strict._._._≋_
d__'8779'__32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> [AgdaAny] -> [AgdaAny] -> ()
d__'8779'__32 = erased
-- Data.List.Relation.Binary.Lex.Strict._._._<_
d__'60'__34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> [AgdaAny] -> [AgdaAny] -> ()
d__'60'__34 = erased
-- Data.List.Relation.Binary.Lex.Strict._._.xs≮[]
d_xs'8814''91''93'_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_xs'8814''91''93'_38 = erased
-- Data.List.Relation.Binary.Lex.Strict._._.¬[]<[]
d_'172''91''93''60''91''93'_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172''91''93''60''91''93'_40 = erased
-- Data.List.Relation.Binary.Lex.Strict._._.<-irreflexive
d_'60''45'irreflexive_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irreflexive_42 = erased
-- Data.List.Relation.Binary.Lex.Strict._._.<-asymmetric
d_'60''45'asymmetric_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'asymmetric_60 = erased
-- Data.List.Relation.Binary.Lex.Strict._._._.irrefl
d_irrefl_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_72 = erased
-- Data.List.Relation.Binary.Lex.Strict._._._.asym
d_asym_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_74 = erased
-- Data.List.Relation.Binary.Lex.Strict._._.<-antisymmetric
d_'60''45'antisymmetric_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'60''45'antisymmetric_102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''45'antisymmetric_102
du_'60''45'antisymmetric_102 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'60''45'antisymmetric_102 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Lex.du_antisymmetric_78 v3
      v4
-- Data.List.Relation.Binary.Lex.Strict._._.<-transitive
d_'60''45'transitive_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
d_'60''45'transitive_104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''45'transitive_104
du_'60''45'transitive_104 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
du_'60''45'transitive_104
  = coe MAlonzo.Code.Data.List.Relation.Binary.Lex.du_transitive_132
-- Data.List.Relation.Binary.Lex.Strict._._.<-compare
d_'60''45'compare_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''45'compare_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_'60''45'compare_106 v6 v7 v8 v9
du_'60''45'compare_106 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_'60''45'compare_106 v0 v1 v2 v3
  = case coe v2 of
      []
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56)
             (:) v4 v5
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                    (coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_halt_48)
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v4 v5
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                    (coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_halt_48)
             (:) v6 v7
               -> let v8 = coe v1 v4 v6 in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v9
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                              (coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60 v9)
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v10
                         -> let v12
                                  = coe
                                      du_'60''45'compare_106 (coe v0) (coe v1) (coe v5) (coe v7) in
                            coe
                              (case coe v12 of
                                 MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v13
                                   -> coe
                                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74
                                           v10 v13)
                                 MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v14
                                   -> coe
                                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                           v10 v14)
                                 MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v15
                                   -> coe
                                        MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74
                                           (coe v0 v4 v6 v10) v15)
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v11
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                              (coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60 v11)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Lex.Strict._._.<-decidable
d_'60''45'decidable_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'60''45'decidable_274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''45'decidable_274
du_'60''45'decidable_274 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'60''45'decidable_274
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Lex.du_decidable_260
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
-- Data.List.Relation.Binary.Lex.Strict._._.<-respects₂
d_'60''45'respects'8322'_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'respects'8322'_276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''45'respects'8322'_276
du_'60''45'respects'8322'_276 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''45'respects'8322'_276
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Lex.du_respects'8322'_180
-- Data.List.Relation.Binary.Lex.Strict._._.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''45'isStrictPartialOrder_278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'isStrictPartialOrder_278 v6
du_'60''45'isStrictPartialOrder_278 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_'60''45'isStrictPartialOrder_278 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_14045
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_isEquivalence_56
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
            (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.du_transitive_132
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
            (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_306 (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.du_respects'8322'_180
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
            (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict._._.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''45'isStrictTotalOrder_314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'isStrictTotalOrder_314 v6
du_'60''45'isStrictTotalOrder_314 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
du_'60''45'isStrictTotalOrder_314 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_24953
      (coe
         du_'60''45'isStrictPartialOrder_278
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
            (coe v0)))
      (coe
         du_'60''45'compare_106
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
                  (coe v0))))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_544 (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict.<-strictPartialOrder
d_'60''45'strictPartialOrder_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_'60''45'strictPartialOrder_374 ~v0 ~v1 ~v2 v3
  = du_'60''45'strictPartialOrder_374 v3
du_'60''45'strictPartialOrder_374 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
du_'60''45'strictPartialOrder_374 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictPartialOrder'46'constructor_11097
      (coe
         du_'60''45'isStrictPartialOrder_278
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
            (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict.<-strictTotalOrder
d_'60''45'strictTotalOrder_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
d_'60''45'strictTotalOrder_442 ~v0 ~v1 ~v2 v3
  = du_'60''45'strictTotalOrder_442 v3
du_'60''45'strictTotalOrder_442 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
du_'60''45'strictTotalOrder_442 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictTotalOrder'46'constructor_21059
      (coe
         du_'60''45'isStrictTotalOrder_314
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
            (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict._.≤-reflexive
d_'8804''45'reflexive_544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
d_'8804''45'reflexive_544 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_'8804''45'reflexive_544 v6 v7 v8
du_'8804''45'reflexive_544 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
du_'8804''45'reflexive_544 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_base_42
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    (:) v11 v12
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74 v7
                           (coe du_'8804''45'reflexive_544 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Lex.Strict._._._≋_
d__'8779'__566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> [AgdaAny] -> [AgdaAny] -> ()
d__'8779'__566 = erased
-- Data.List.Relation.Binary.Lex.Strict._._._≤_
d__'8804'__568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> [AgdaAny] -> [AgdaAny] -> ()
d__'8804'__568 = erased
-- Data.List.Relation.Binary.Lex.Strict._._.≤-antisymmetric
d_'8804''45'antisymmetric_570 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'8804''45'antisymmetric_570 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''45'antisymmetric_570
du_'8804''45'antisymmetric_570 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'8804''45'antisymmetric_570 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Lex.du_antisymmetric_78 v3
      v4
-- Data.List.Relation.Binary.Lex.Strict._._.≤-transitive
d_'8804''45'transitive_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
d_'8804''45'transitive_572 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''45'transitive_572
du_'8804''45'transitive_572 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
du_'8804''45'transitive_572
  = coe MAlonzo.Code.Data.List.Relation.Binary.Lex.du_transitive_132
-- Data.List.Relation.Binary.Lex.Strict._._.≤-total
d_'8804''45'total_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  [AgdaAny] -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'total_574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_'8804''45'total_574 v6 v7 v8 v9
du_'8804''45'total_574 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  [AgdaAny] -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8804''45'total_574 v0 v1 v2 v3
  = case coe v2 of
      []
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_base_42
                       (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
             (:) v4 v5
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_halt_48)
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v4 v5
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_halt_48)
             (:) v6 v7
               -> let v8 = coe v1 v4 v6 in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v9
                         -> coe
                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                              (coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60 v9)
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v10
                         -> let v12
                                  = coe
                                      du_'8804''45'total_574 (coe v0) (coe v1) (coe v5) (coe v7) in
                            coe
                              (case coe v12 of
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                                   -> coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74
                                           v10 v13)
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                                   -> coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                        (coe
                                           MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_next_74
                                           (coe v0 v4 v6 v10) v13)
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v11
                         -> coe
                              MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                              (coe MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.C_this_60 v11)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Lex.Strict._._.≤-decidable
d_'8804''45'decidable_678 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8804''45'decidable_678 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''45'decidable_678
du_'8804''45'decidable_678 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8804''45'decidable_678
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Lex.du_decidable_260
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
         (coe
            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Data.List.Relation.Binary.Lex.Strict._._.≤-respects₂
d_'8804''45'respects'8322'_680 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8804''45'respects'8322'_680 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''45'respects'8322'_680
du_'8804''45'respects'8322'_680 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8804''45'respects'8322'_680
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Lex.du_respects'8322'_180
-- Data.List.Relation.Binary.Lex.Strict._._.≤-isPreorder
d_'8804''45'isPreorder_682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8804''45'isPreorder_682 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_'8804''45'isPreorder_682 v6 v7 v8
du_'8804''45'isPreorder_682 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_'8804''45'isPreorder_682 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_isEquivalence_56
         (coe v0))
      (coe du_'8804''45'reflexive_544)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.du_transitive_132
         (coe v0) (coe v2) (coe v1))
-- Data.List.Relation.Binary.Lex.Strict._._.≤-isPartialOrder
d_'8804''45'isPartialOrder_690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_'8804''45'isPartialOrder_690 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8804''45'isPartialOrder_690 v6
du_'8804''45'isPartialOrder_690 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_'8804''45'isPartialOrder_690 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_9853
      (coe
         du_'8804''45'isPreorder_682
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
            (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_306 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
            (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.du_antisymmetric_78)
-- Data.List.Relation.Binary.Lex.Strict._._.≤-isDecPartialOrder
d_'8804''45'isDecPartialOrder_726 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
d_'8804''45'isDecPartialOrder_726 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8804''45'isDecPartialOrder_726 v6
du_'8804''45'isDecPartialOrder_726 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
du_'8804''45'isDecPartialOrder_726 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecPartialOrder'46'constructor_11683
      (coe
         du_'8804''45'isPartialOrder_690
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
            (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du__'8799'__562 (coe v0)))
      (coe
         du_'8804''45'decidable_678
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du__'8799'__562 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du__'60''63'__564
            (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict._._.≤-isTotalOrder
d_'8804''45'isTotalOrder_780 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
d_'8804''45'isTotalOrder_780 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8804''45'isTotalOrder_780 v6
du_'8804''45'isTotalOrder_780 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
du_'8804''45'isTotalOrder_780 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalOrder'46'constructor_20555
      (coe
         du_'8804''45'isPartialOrder_690
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
            (coe v0)))
      (coe
         du_'8804''45'total_574
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
                  (coe v0))))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_544 (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict._._.≤-isDecTotalOrder
d_'8804''45'isDecTotalOrder_834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
d_'8804''45'isDecTotalOrder_834 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8804''45'isDecTotalOrder_834 v6
du_'8804''45'isDecTotalOrder_834 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
du_'8804''45'isDecTotalOrder_834 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecTotalOrder'46'constructor_22695
      (coe du_'8804''45'isTotalOrder_780 (coe v0))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du__'8799'__562 (coe v0)))
      (coe
         du_'8804''45'decidable_678
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du__'8799'__562 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du__'60''63'__564
            (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict.≤-preorder
d_'8804''45'preorder_894 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_'8804''45'preorder_894 ~v0 ~v1 ~v2 v3
  = du_'8804''45'preorder_894 v3
du_'8804''45'preorder_894 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_'8804''45'preorder_894 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2267
      (coe
         du_'8804''45'isPreorder_682
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0)))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_84
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0)))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_118
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0))))
-- Data.List.Relation.Binary.Lex.Strict.≤-partialOrder
d_'8804''45'partialOrder_970 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_'8804''45'partialOrder_970 ~v0 ~v1 ~v2 v3
  = du_'8804''45'partialOrder_970 v3
du_'8804''45'partialOrder_970 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_'8804''45'partialOrder_970 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_6389
      (coe
         du_'8804''45'isPartialOrder_690
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
            (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict.≤-decPoset
d_'8804''45'decPoset_1038 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecPoset_406
d_'8804''45'decPoset_1038 ~v0 ~v1 ~v2 v3
  = du_'8804''45'decPoset_1038 v3
du_'8804''45'decPoset_1038 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecPoset_406
du_'8804''45'decPoset_1038 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecPoset'46'constructor_8213
      (coe
         du_'8804''45'isDecPartialOrder_726
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
            (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict.≤-decTotalOrder
d_'8804''45'decTotalOrder_1130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
d_'8804''45'decTotalOrder_1130 ~v0 ~v1 ~v2 v3
  = du_'8804''45'decTotalOrder_1130 v3
du_'8804''45'decTotalOrder_1130 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
du_'8804''45'decTotalOrder_1130 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecTotalOrder'46'constructor_17849
      (coe
         du_'8804''45'isDecTotalOrder_834
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
            (coe v0)))
