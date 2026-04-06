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

module MAlonzo.Code.Data.List.Relation.Binary.Pointwise where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core

-- Data.List.Relation.Binary.Pointwise.isEquivalence
d_isEquivalence_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_56 ~v0 ~v1 ~v2 ~v3 v4 = du_isEquivalence_56 v4
du_isEquivalence_56 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_56 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_46
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_refl_30
         (coe MAlonzo.Code.Relation.Binary.Structures.d_refl_36 (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_symmetric_40
         (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_38 (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_transitive_50
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_40 (coe v0)))
-- Data.List.Relation.Binary.Pointwise.isDecEquivalence
d_isDecEquivalence_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_isDecEquivalence_76 ~v0 ~v1 ~v2 ~v3 v4
  = du_isDecEquivalence_76 v4
du_isDecEquivalence_76 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_isDecEquivalence_76 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_70
      (coe
         du_isEquivalence_56
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
            (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__56 (coe v0)))
-- Data.List.Relation.Binary.Pointwise.isPreorder
d_isPreorder_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isPreorder_100 v6
du_isPreorder_100 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_isPreorder_100 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         du_isEquivalence_56
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_reflexive_28
         (MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88 (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_transitive_50
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_90 (coe v0)))
-- Data.List.Relation.Binary.Pointwise.isPartialOrder
d_isPartialOrder_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_142 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialOrder_142 v6
du_isPartialOrder_142 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_isPartialOrder_142 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         du_isPreorder_100
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v0)))
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_antisymmetric_64
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_antisym_258 (coe v0)))
-- Data.List.Relation.Binary.Pointwise.setoid
d_setoid_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_188 ~v0 ~v1 v2 = du_setoid_188 v2
du_setoid_188 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_188 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      (coe
         du_isEquivalence_56
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v0)))
-- Data.List.Relation.Binary.Pointwise.decSetoid
d_decSetoid_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_decSetoid_192 ~v0 ~v1 v2 = du_decSetoid_192 v2
du_decSetoid_192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
du_decSetoid_192 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_134
      (coe
         du_isDecEquivalence_76
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_106
            (coe v0)))
-- Data.List.Relation.Binary.Pointwise.preorder
d_preorder_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_preorder_196 ~v0 ~v1 ~v2 v3 = du_preorder_196 v3
du_preorder_196 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_preorder_196 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_232
      (coe
         du_isPreorder_100
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0)))
-- Data.List.Relation.Binary.Pointwise.poset
d_poset_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_200 ~v0 ~v1 ~v2 v3 = du_poset_200 v3
du_poset_200 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_200 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      (coe
         du_isPartialOrder_142
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
            (coe v0)))
-- Data.List.Relation.Binary.Pointwise.All-resp-Pointwise
d_All'45'resp'45'Pointwise_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_All'45'resp'45'Pointwise_206 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                               v10
  = du_All'45'resp'45'Pointwise_206 v6 v7 v8 v9 v10
du_All'45'resp'45'Pointwise_206 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_All'45'resp'45'Pointwise_206 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe
             seq (coe v4)
             (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50)
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v2 of
                    (:) v13 v14
                      -> case coe v4 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v17 v18
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe v0 v11 v13 v9 v17)
                                  (coe
                                     du_All'45'resp'45'Pointwise_206 (coe v0) (coe v12) (coe v14)
                                     (coe v10) (coe v18))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.Any-resp-Pointwise
d_Any'45'resp'45'Pointwise_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_Any'45'resp'45'Pointwise_222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                               v10
  = du_Any'45'resp'45'Pointwise_222 v6 v7 v8 v9 v10
du_Any'45'resp'45'Pointwise_222 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_Any'45'resp'45'Pointwise_222 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v2 of
                    (:) v13 v14
                      -> case coe v4 of
                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v17
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                  (coe v0 v11 v13 v9 v17)
                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v17
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                  (coe
                                     du_Any'45'resp'45'Pointwise_222 (coe v0) (coe v12) (coe v14)
                                     (coe v10) (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.AllPairs-resp-Pointwise
d_AllPairs'45'resp'45'Pointwise_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_AllPairs'45'resp'45'Pointwise_240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                    v8 v9 v10
  = du_AllPairs'45'resp'45'Pointwise_240 v6 v7 v8 v9 v10
du_AllPairs'45'resp'45'Pointwise_240 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_AllPairs'45'resp'45'Pointwise_240 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe
             seq (coe v4)
             (coe
                MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C_'91''93'_22)
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v2 of
                    (:) v13 v14
                      -> case coe v0 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                             -> case coe v4 of
                                  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28 v19 v20
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                                         (coe
                                            du_All'45'resp'45'Pointwise_206 (coe v15 v13) (coe v12)
                                            (coe v14) (coe v10)
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
                                               (coe (\ v21 -> coe v16 v21 v11 v13 v9)) (coe v12)
                                               (coe v19)))
                                         (coe
                                            du_AllPairs'45'resp'45'Pointwise_240 (coe v0) (coe v12)
                                            (coe v14) (coe v10) (coe v20))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.tabulate⁺
d_tabulate'8314'_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_tabulate'8314'_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9
  = du_tabulate'8314'_264 v6 v9
du_tabulate'8314'_264 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_tabulate'8314'_264 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                (coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                (coe
                   du_tabulate'8314'_264 (coe v2)
                   (coe
                      (\ v3 -> coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v3)))))
-- Data.List.Relation.Binary.Pointwise.tabulate⁻
d_tabulate'8315'_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_tabulate'8315'_280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_tabulate'8315'_280 v9 v10
du_tabulate'8315'_280 ::
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_tabulate'8315'_280 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v6 v7
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v6
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v9
               -> coe du_tabulate'8315'_280 (coe v7) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.++⁺
d_'43''43''8314'_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''8314'_296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10 v11
  = du_'43''43''8314'_296 v6 v7 v10 v11
du_'43''43''8314'_296 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''8314'_296 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe v3
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v1 of
                    (:) v12 v13
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                           v8
                           (coe du_'43''43''8314'_296 (coe v11) (coe v13) (coe v9) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.++-cancelˡ
d_'43''43''45'cancel'737'_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''45'cancel'737'_308 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_'43''43''45'cancel'737'_308 v6 v7
du_'43''43''45'cancel'737'_308 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''45'cancel'737'_308 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v8 v9
               -> coe du_'43''43''45'cancel'737'_308 (coe v3) (coe v9)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.++-cancelʳ
d_'43''43''45'cancel'691'_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''45'cancel'691'_322 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_'43''43''45'cancel'691'_322 v5 v6 v7
du_'43''43''45'cancel'691'_322 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''45'cancel'691'_322 v0 v1 v2
  = case coe v0 of
      []
        -> case coe v1 of
             []
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
             (:) v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                    erased
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v3 v4
        -> case coe v1 of
             []
               -> coe
                    MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                    erased
             (:) v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v11 v12
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                           v11
                           (coe du_'43''43''45'cancel'691'_322 (coe v4) (coe v6) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise._.++⁺ˡ
d_'43''43''8314''737'_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''8314''737'_364 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7
  = du_'43''43''8314''737'_364 v4 v5
du_'43''43''8314''737'_364 ::
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''8314''737'_364 v0 v1
  = coe
      du_'43''43''8314'_296 (coe v1) (coe v1)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_refl_30
         (coe v0) (coe v1))
-- Data.List.Relation.Binary.Pointwise._.++⁺ʳ
d_'43''43''8314''691'_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''8314''691'_372 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8
  = du_'43''43''8314''691'_372 v4 v5 v6 v7 v8
du_'43''43''8314''691'_372 ::
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''8314''691'_372 v0 v1 v2 v3 v4
  = coe
      du_'43''43''8314'_296 (coe v2) (coe v3) (coe v4)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_refl_30
         (coe v0) (coe v1))
-- Data.List.Relation.Binary.Pointwise.concat⁺
d_concat'8314'_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [[AgdaAny]] ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_concat'8314'_382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_concat'8314'_382 v6 v7 v8
du_concat'8314'_382 ::
  [[AgdaAny]] ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_concat'8314'_382 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe v2
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    (:) v11 v12
                      -> coe
                           du_'43''43''8314'_296 (coe v9) (coe v11) (coe v7)
                           (coe du_concat'8314'_382 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.reverseAcc⁺
d_reverseAcc'8314'_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_reverseAcc'8314'_388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
                       v11
  = du_reverseAcc'8314'_388 v8 v9 v10 v11
du_reverseAcc'8314'_388 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_reverseAcc'8314'_388 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe v2
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v1 of
                    (:) v12 v13
                      -> coe
                           du_reverseAcc'8314'_388 (coe v11) (coe v13)
                           (coe
                              MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                              v8 v2)
                           (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.ʳ++⁺
d_'691''43''43''8314'_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'691''43''43''8314'_398 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9 v10
                          v11
  = du_'691''43''43''8314'_398 v6 v7 v10 v11
du_'691''43''43''8314'_398 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'691''43''43''8314'_398 v0 v1 v2 v3
  = coe du_reverseAcc'8314'_388 (coe v0) (coe v1) (coe v3) (coe v2)
-- Data.List.Relation.Binary.Pointwise.reverse⁺
d_reverse'8314'_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_reverse'8314'_404 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_reverse'8314'_404 v6 v7
du_reverse'8314'_404 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_reverse'8314'_404 v0 v1
  = coe
      du_reverseAcc'8314'_388 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56)
-- Data.List.Relation.Binary.Pointwise.map⁺
d_map'8314'_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_map'8314'_414 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                ~v12 ~v13 v14
  = du_map'8314'_414 v10 v11 v14
du_map'8314'_414 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_map'8314'_414 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe v2
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    (:) v11 v12
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                           v7 (coe du_map'8314'_414 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.map⁻
d_map'8315'_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_map'8315'_436 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                ~v12 ~v13 v14
  = du_map'8315'_436 v10 v11 v14
du_map'8315'_436 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_map'8315'_436 v0 v1 v2
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe
                seq (coe v2)
                (coe
                   MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56))
      (:) v3 v4
        -> case coe v1 of
             (:) v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v11 v12
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                           v11 (coe du_map'8315'_436 (coe v4) (coe v6) (coe v12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.foldr⁺
d_foldr'8314'_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  AgdaAny
d_foldr'8314'_466 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11 v12
                  v13 v14
  = du_foldr'8314'_466 v6 v7 v8 v9 v10 v11 v12 v13 v14
du_foldr'8314'_466 ::
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  AgdaAny
du_foldr'8314'_466 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v8 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe v7
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v13 v14
        -> case coe v0 of
             (:) v15 v16
               -> case coe v1 of
                    (:) v17 v18
                      -> coe
                           v4 v15 v17
                           (coe
                              MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v2) (coe v5)
                              (coe v16))
                           (coe
                              MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v3) (coe v6)
                              (coe v18))
                           v13
                           (coe
                              du_foldr'8314'_466 (coe v16) (coe v18) (coe v2) (coe v3) (coe v4)
                              (coe v5) (coe v6) (coe v7) (coe v14))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise._.filter⁺
d_filter'8314'_512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_filter'8314'_512 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                   ~v12 ~v13 v14 v15 v16
  = du_filter'8314'_512 v10 v11 v14 v15 v16
du_filter'8314'_512 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_filter'8314'_512 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe v4
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v9 v10
        -> case coe v2 of
             (:) v11 v12
               -> case coe v3 of
                    (:) v13 v14
                      -> let v15 = coe v0 v11 in
                         coe
                           (let v16 = coe v1 v13 in
                            coe
                              (case coe v15 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                   -> if coe v17
                                        then case coe v16 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                 -> if coe v19
                                                      then coe
                                                             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                                             v9
                                                             (coe
                                                                du_filter'8314'_512 (coe v0)
                                                                (coe v1) (coe v12) (coe v14)
                                                                (coe v10))
                                                      else coe
                                                             seq (coe v18)
                                                             (coe
                                                                seq (coe v20)
                                                                (coe
                                                                   MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                   erased))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        else (case coe v16 of
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                  -> if coe v19
                                                       then coe
                                                              seq (coe v18)
                                                              (coe
                                                                 seq (coe v20)
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                    erased))
                                                       else coe
                                                              du_filter'8314'_512 (coe v0) (coe v1)
                                                              (coe v12) (coe v14) (coe v10)
                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.replicate⁺
d_replicate'8314'_568 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_replicate'8314'_568 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_replicate'8314'_568 v8 v9
du_replicate'8314'_568 ::
  AgdaAny ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_replicate'8314'_568 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                v0 (coe du_replicate'8314'_568 (coe v0) (coe v2)))
-- Data.List.Relation.Binary.Pointwise.lookup⁻
d_lookup'8315'_580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_lookup'8315'_580 ~v0 ~v1 v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_lookup'8315'_580 v2 v5 v9
du_lookup'8315'_580 ::
  [AgdaAny] ->
  [AgdaAny] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_lookup'8315'_580 v0 v1 v2
  = case coe v0 of
      []
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56)
      (:) v3 v4
        -> case coe v1 of
             (:) v5 v6
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                    (coe
                       v2 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) erased)
                    (coe
                       du_lookup'8315'_580 (coe v4) (coe v6)
                       (coe
                          (\ v7 v8 v9 ->
                             coe
                               v2 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v7)
                               (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v8) erased)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.lookup⁺
d_lookup'8314'_592 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_lookup'8314'_592 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_lookup'8314'_592 v6 v7 v8 v9
du_lookup'8314'_592 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_lookup'8314'_592 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v8 v9
        -> case coe v0 of
             (:) v10 v11
               -> case coe v1 of
                    (:) v12 v13
                      -> case coe v3 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v8
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v15
                             -> coe du_lookup'8314'_592 (coe v11) (coe v13) (coe v9) (coe v15)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Pointwise.Pointwise-≡⇒≡
d_Pointwise'45''8801''8658''8801'_600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Pointwise'45''8801''8658''8801'_600 = erased
-- Data.List.Relation.Binary.Pointwise.≡⇒Pointwise-≡
d_'8801''8658'Pointwise'45''8801'_606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'8801''8658'Pointwise'45''8801'_606 ~v0 ~v1 v2 ~v3 ~v4
  = du_'8801''8658'Pointwise'45''8801'_606 v2
du_'8801''8658'Pointwise'45''8801'_606 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'8801''8658'Pointwise'45''8801'_606 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_refl_30
      erased (coe v0)
-- Data.List.Relation.Binary.Pointwise.Pointwise-≡↔≡
d_Pointwise'45''8801''8596''8801'_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_Pointwise'45''8801''8596''8801'_608 ~v0 ~v1
  = du_Pointwise'45''8801''8596''8801'_608
du_Pointwise'45''8801''8596''8801'_608 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_Pointwise'45''8801''8596''8801'_608
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2220 (coe (\ v0 -> v0))
      (coe (\ v0 -> v0)) erased
      (\ v0 v1 v2 -> coe du_'8801''8658'Pointwise'45''8801'_606 v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe
            (\ v0 v1 v2 ->
               coe du_'8801''8658'Pointwise'45''8801'_606 (coe v1))))
