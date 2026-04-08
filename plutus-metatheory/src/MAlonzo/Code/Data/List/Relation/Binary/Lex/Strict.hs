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

module MAlonzo.Code.Data.List.Relation.Binary.Lex.Strict where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Lex
import qualified MAlonzo.Code.Data.List.Relation.Binary.Lex.Core
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

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
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
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
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
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
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'respects'8322'_276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''45'respects'8322'_276
du_'60''45'respects'8322'_276 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
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
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_'60''45'isStrictPartialOrder_278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'isStrictPartialOrder_278 v6
du_'60''45'isStrictPartialOrder_278 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
du_'60''45'isStrictPartialOrder_278 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_412
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_isEquivalence_56
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
            (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.du_transitive_132
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
            (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_386 (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.du_respects'8322'_180
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
            (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict._._.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_'60''45'isStrictTotalOrder_314 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''45'isStrictTotalOrder_314 v6
du_'60''45'isStrictTotalOrder_314 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
du_'60''45'isStrictTotalOrder_314 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_680
      (coe
         du_'60''45'isStrictPartialOrder_278
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
            (coe v0)))
      (coe
         du_'60''45'compare_106
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
                  (coe v0))))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_634 (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict.<-strictPartialOrder
d_'60''45'strictPartialOrder_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
d_'60''45'strictPartialOrder_374 ~v0 ~v1 ~v2 v3
  = du_'60''45'strictPartialOrder_374 v3
du_'60''45'strictPartialOrder_374 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
du_'60''45'strictPartialOrder_374 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_842
      (coe
         du_'60''45'isStrictPartialOrder_278
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_782
            (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict.<-strictTotalOrder
d_'60''45'strictTotalOrder_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
d_'60''45'strictTotalOrder_450 ~v0 ~v1 ~v2 v3
  = du_'60''45'strictTotalOrder_450 v3
du_'60''45'strictTotalOrder_450 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
du_'60''45'strictTotalOrder_450 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1386
      (coe
         du_'60''45'isStrictTotalOrder_314
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1302
            (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict._.≤-reflexive
d_'8804''45'reflexive_560 ::
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
d_'8804''45'reflexive_560 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_'8804''45'reflexive_560 v6 v7 v8
du_'8804''45'reflexive_560 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
du_'8804''45'reflexive_560 v0 v1 v2
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
                           (coe du_'8804''45'reflexive_560 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Lex.Strict._._._≋_
d__'8779'__582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> [AgdaAny] -> [AgdaAny] -> ()
d__'8779'__582 = erased
-- Data.List.Relation.Binary.Lex.Strict._._._≤_
d__'8804'__584 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> [AgdaAny] -> [AgdaAny] -> ()
d__'8804'__584 = erased
-- Data.List.Relation.Binary.Lex.Strict._._.≤-antisymmetric
d_'8804''45'antisymmetric_586 ::
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
d_'8804''45'antisymmetric_586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''45'antisymmetric_586
du_'8804''45'antisymmetric_586 ::
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
du_'8804''45'antisymmetric_586 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Lex.du_antisymmetric_78 v3
      v4
-- Data.List.Relation.Binary.Lex.Strict._._.≤-transitive
d_'8804''45'transitive_588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
d_'8804''45'transitive_588 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''45'transitive_588
du_'8804''45'transitive_588 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Lex.Core.T_Lex_32
du_'8804''45'transitive_588
  = coe MAlonzo.Code.Data.List.Relation.Binary.Lex.du_transitive_132
-- Data.List.Relation.Binary.Lex.Strict._._.≤-total
d_'8804''45'total_590 ::
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
d_'8804''45'total_590 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_'8804''45'total_590 v6 v7 v8 v9
du_'8804''45'total_590 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  [AgdaAny] -> [AgdaAny] -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8804''45'total_590 v0 v1 v2 v3
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
                                      du_'8804''45'total_590 (coe v0) (coe v1) (coe v5) (coe v7) in
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
d_'8804''45'decidable_694 ::
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
d_'8804''45'decidable_694 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''45'decidable_694
du_'8804''45'decidable_694 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8804''45'decidable_694
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Lex.du_decidable_260
      (coe
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
         (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
         (coe
            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Data.List.Relation.Binary.Lex.Strict._._.≤-respects₂
d_'8804''45'respects'8322'_696 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8804''45'respects'8322'_696 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''45'respects'8322'_696
du_'8804''45'respects'8322'_696 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8804''45'respects'8322'_696
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Lex.du_respects'8322'_180
-- Data.List.Relation.Binary.Lex.Strict._._.≤-isPreorder
d_'8804''45'isPreorder_698 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_'8804''45'isPreorder_698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_'8804''45'isPreorder_698 v6 v7 v8
du_'8804''45'isPreorder_698 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_'8804''45'isPreorder_698 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_isEquivalence_56
         (coe v0))
      (coe du_'8804''45'reflexive_560)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.du_transitive_132
         (coe v0) (coe v2) (coe v1))
-- Data.List.Relation.Binary.Lex.Strict._._.≤-isPartialOrder
d_'8804''45'isPartialOrder_706 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_'8804''45'isPartialOrder_706 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8804''45'isPartialOrder_706 v6
du_'8804''45'isPartialOrder_706 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_'8804''45'isPartialOrder_706 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         du_'8804''45'isPreorder_698
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
            (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_386 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
            (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.du_antisymmetric_78)
-- Data.List.Relation.Binary.Lex.Strict._._.≤-isDecPartialOrder
d_'8804''45'isDecPartialOrder_742 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
d_'8804''45'isDecPartialOrder_742 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8804''45'isDecPartialOrder_742 v6
du_'8804''45'isDecPartialOrder_742 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
du_'8804''45'isDecPartialOrder_742 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_364
      (coe
         du_'8804''45'isPartialOrder_706
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
            (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du__'8799'__652 (coe v0)))
      (coe
         du_'8804''45'decidable_694
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du__'8799'__652 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du__'60''63'__654
            (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict._._.≤-isTotalOrder
d_'8804''45'isTotalOrder_796 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_'8804''45'isTotalOrder_796 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8804''45'isTotalOrder_796 v6
du_'8804''45'isTotalOrder_796 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
du_'8804''45'isTotalOrder_796 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_540
      (coe
         du_'8804''45'isPartialOrder_706
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
            (coe v0)))
      (coe
         du_'8804''45'total_590
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
                  (coe v0))))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_634 (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict._._.≤-isDecTotalOrder
d_'8804''45'isDecTotalOrder_850 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_'8804''45'isDecTotalOrder_850 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8804''45'isDecTotalOrder_850 v6
du_'8804''45'isDecTotalOrder_850 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
du_'8804''45'isDecTotalOrder_850 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_618
      (coe du_'8804''45'isTotalOrder_796 (coe v0))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du__'8799'__652 (coe v0)))
      (coe
         du_'8804''45'decidable_694
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du__'8799'__652 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du__'60''63'__654
            (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict.≤-preorder
d_'8804''45'preorder_910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_'8804''45'preorder_910 ~v0 ~v1 ~v2 v3
  = du_'8804''45'preorder_910 v3
du_'8804''45'preorder_910 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_'8804''45'preorder_910 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_232
      (coe
         du_'8804''45'isPreorder_698
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0)))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_90
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0)))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.du_'8764''45'resp'45''8776'_124
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0))))
-- Data.List.Relation.Binary.Lex.Strict.≤-partialOrder
d_'8804''45'partialOrder_994 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_'8804''45'partialOrder_994 ~v0 ~v1 ~v2 v3
  = du_'8804''45'partialOrder_994 v3
du_'8804''45'partialOrder_994 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_'8804''45'partialOrder_994 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      (coe
         du_'8804''45'isPartialOrder_706
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_782
            (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict.≤-decPoset
d_'8804''45'decPoset_1070 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecPoset_596
d_'8804''45'decPoset_1070 ~v0 ~v1 ~v2 v3
  = du_'8804''45'decPoset_1070 v3
du_'8804''45'decPoset_1070 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecPoset_596
du_'8804''45'decPoset_1070 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_752
      (coe
         du_'8804''45'isDecPartialOrder_742
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1302
            (coe v0)))
-- Data.List.Relation.Binary.Lex.Strict.≤-decTotalOrder
d_'8804''45'decTotalOrder_1170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
d_'8804''45'decTotalOrder_1170 ~v0 ~v1 ~v2 v3
  = du_'8804''45'decTotalOrder_1170 v3
du_'8804''45'decTotalOrder_1170 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
du_'8804''45'decTotalOrder_1170 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1272
      (coe
         du_'8804''45'isDecTotalOrder_850
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1302
            (coe v0)))
