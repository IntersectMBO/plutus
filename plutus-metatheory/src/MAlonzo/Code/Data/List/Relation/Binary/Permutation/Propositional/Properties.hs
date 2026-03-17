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

module MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Membership.Propositional.Properties
import qualified MAlonzo.Code.Data.List.Membership.Setoid.Properties
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.List.Relation.Binary.Permutation.Propositional.Properties.↭-empty-inv
d_'8621''45'empty'45'inv_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8621''45'empty'45'inv_30 = erased
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.¬x∷xs↭[]
d_'172'x'8759'xs'8621''91''93'_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'x'8759'xs'8621''91''93'_44 = erased
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.↭-singleton-inv
d_'8621''45'singleton'45'inv_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8621''45'singleton'45'inv_62 = erased
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.↭-sym-involutive
d_'8621''45'sym'45'involutive_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8621''45'sym'45'involutive_84 = erased
-- Data.List.Relation.Binary.Permutation.Propositional.Properties._.All-resp-↭
d_All'45'resp'45''8621'_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_All'45'resp'45''8621'_110 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_All'45'resp'45''8621'_110 v4 v5 v6 v7
du_All'45'resp'45''8621'_110 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_All'45'resp'45''8621'_110 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
        -> coe v3
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    (:) v10 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v14 v15
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v14
                                  (coe
                                     du_All'45'resp'45''8621'_110 (coe v9) (coe v11) (coe v7)
                                     (coe v15))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v10 of
                    (:) v11 v12
                      -> case coe v1 of
                           (:) v13 v14
                             -> case coe v14 of
                                  (:) v15 v16
                                    -> case coe v3 of
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v19 v20
                                           -> case coe v20 of
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v23 v24
                                                  -> coe
                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                       v23
                                                       (coe
                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                          v19
                                                          (coe
                                                             du_All'45'resp'45''8621'_110 (coe v12)
                                                             (coe v16) (coe v8) (coe v24)))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48 v5 v7 v8
        -> coe
             du_All'45'resp'45''8621'_110 (coe v5) (coe v1) (coe v8)
             (coe
                du_All'45'resp'45''8621'_110 (coe v0) (coe v5) (coe v7) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties._.Any-resp-↭
d_Any'45'resp'45''8621'_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_Any'45'resp'45''8621'_140 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_Any'45'resp'45''8621'_140 v4 v5 v6 v7
du_Any'45'resp'45''8621'_140 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_Any'45'resp'45''8621'_140 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
        -> coe v3
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    (:) v10 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v14
                             -> coe MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v14
                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v14
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                  (coe
                                     du_Any'45'resp'45''8621'_140 (coe v9) (coe v11) (coe v7)
                                     (coe v14))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v10 of
                    (:) v11 v12
                      -> case coe v1 of
                           (:) v13 v14
                             -> case coe v14 of
                                  (:) v15 v16
                                    -> case coe v3 of
                                         MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v19
                                           -> coe
                                                MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                   v19)
                                         MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v19
                                           -> case coe v19 of
                                                MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v22
                                                  -> coe
                                                       MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                       v22
                                                MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v22
                                                  -> coe
                                                       MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                       (coe
                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                          (coe
                                                             du_Any'45'resp'45''8621'_140 (coe v12)
                                                             (coe v16) (coe v8) (coe v22)))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48 v5 v7 v8
        -> coe
             du_Any'45'resp'45''8621'_140 (coe v5) (coe v1) (coe v8)
             (coe
                du_Any'45'resp'45''8621'_140 (coe v0) (coe v5) (coe v7) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties._.Any-resp-[σ⁻¹∘σ]
d_Any'45'resp'45''91'σ'8315''185''8728'σ'93'_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Any'45'resp'45''91'σ'8315''185''8728'σ'93'_194 = erased
-- Data.List.Relation.Binary.Permutation.Propositional.Properties._.Any-resp-[σ∘σ⁻¹]
d_Any'45'resp'45''91'σ'8728'σ'8315''185''93'_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_Any'45'resp'45''91'σ'8728'σ'8315''185''93'_236 = erased
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.∈-resp-↭
d_'8712''45'resp'45''8621'_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'8712''45'resp'45''8621'_254 ~v0 ~v1 ~v2 v3 v4
  = du_'8712''45'resp'45''8621'_254 v3 v4
du_'8712''45'resp'45''8621'_254 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'8712''45'resp'45''8621'_254 v0 v1
  = coe du_Any'45'resp'45''8621'_140 (coe v0) (coe v1)
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.∈-resp-[σ⁻¹∘σ]
d_'8712''45'resp'45''91'σ'8315''185''8728'σ'93'_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8712''45'resp'45''91'σ'8315''185''8728'σ'93'_266 = erased
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.∈-resp-[σ∘σ⁻¹]
d_'8712''45'resp'45''91'σ'8728'σ'8315''185''93'_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8712''45'resp'45''91'σ'8728'σ'8315''185''93'_278 = erased
-- Data.List.Relation.Binary.Permutation.Propositional.Properties._.map⁺
d_map'8314'_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_map'8314'_294 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_map'8314'_294 v4 v5 v6 v7
du_map'8314'_294 ::
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_map'8314'_294 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40 v7
        -> case coe v1 of
             (:) v8 v9
               -> case coe v2 of
                    (:) v10 v11
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                           (coe du_map'8314'_294 (coe v0) (coe v9) (coe v11) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46 v8
        -> case coe v1 of
             (:) v9 v10
               -> case coe v10 of
                    (:) v11 v12
                      -> case coe v2 of
                           (:) v13 v14
                             -> case coe v14 of
                                  (:) v15 v16
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46
                                         (coe
                                            du_map'8314'_294 (coe v0) (coe v12) (coe v16) (coe v8))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48
             (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v0) (coe v5))
             (coe du_map'8314'_294 (coe v0) (coe v1) (coe v5) (coe v7))
             (coe du_map'8314'_294 (coe v0) (coe v5) (coe v2) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties._.↭-map-inv
d_'8621''45'map'45'inv_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8621''45'map'45'inv_316 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7
  = du_'8621''45'map'45'inv_316 v5 v6 v7
du_'8621''45'map'45'inv_316 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8621''45'map'45'inv_316 v0 v1 v2
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.Product.Base.du_'45''44'__92 (coe v0)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                (coe
                   MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50))
      (:) v3 v4
        -> case coe v4 of
             []
               -> coe
                    MAlonzo.Code.Data.Product.Base.du_'45''44'__92 (coe v0)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                       (coe
                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50))
             (:) v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
                      -> coe
                           MAlonzo.Code.Data.Product.Base.du_'45''44'__92 (coe v0)
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                              (coe
                                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50))
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40 v10
                      -> case coe v1 of
                           (:) v11 v12
                             -> let v13
                                      = coe
                                          du_'8621''45'map'45'inv_316 (coe v4) (coe v12)
                                          (coe v10) in
                                coe
                                  (case coe v13 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                       -> case coe v15 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                              -> coe
                                                   MAlonzo.Code.Data.Product.Base.du_'45''44'__92
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe v3) (coe v14))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      erased
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                         v17))
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46 v11
                      -> case coe v1 of
                           (:) v12 v13
                             -> case coe v13 of
                                  (:) v14 v15
                                    -> let v16
                                             = coe
                                                 du_'8621''45'map'45'inv_316 (coe v6) (coe v15)
                                                 (coe v11) in
                                       coe
                                         (case coe v16 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                              -> case coe v18 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                     -> coe
                                                          MAlonzo.Code.Data.Product.Base.du_'45''44'__92
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                             (coe v5)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                (coe v3) (coe v17)))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             erased
                                                             (coe
                                                                MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46
                                                                v20))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48 v8 v10 v11
                      -> let v12
                               = coe du_'8621''45'map'45'inv_316 (coe v0) (coe v8) (coe v10) in
                         coe
                           (case coe v12 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                -> case coe v14 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> let v17
                                                = coe
                                                    du_'8621''45'map'45'inv_316 (coe v13) (coe v1)
                                                    (coe v11) in
                                          coe
                                            (case coe v17 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                 -> case coe v19 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                        -> coe
                                                             MAlonzo.Code.Data.Product.Base.du_'45''44'__92
                                                             (coe v18)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                erased
                                                                (coe
                                                                   MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48
                                                                   v13 v16 v21))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.↭-length
d_'8621''45'length_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8621''45'length_360 = erased
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.++⁺ˡ
d_'43''43''8314''737'_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_'43''43''8314''737'_382 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_'43''43''8314''737'_382 v2 v5
du_'43''43''8314''737'_382 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_'43''43''8314''737'_382 v0 v1
  = case coe v0 of
      [] -> coe v1
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
             (coe du_'43''43''8314''737'_382 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.++⁺ʳ
d_'43''43''8314''691'_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_'43''43''8314''691'_398 ~v0 ~v1 v2 v3 v4 v5
  = du_'43''43''8314''691'_398 v2 v3 v4 v5
du_'43''43''8314''691'_398 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_'43''43''8314''691'_398 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    (:) v10 v11
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                           (coe
                              du_'43''43''8314''691'_398 (coe v9) (coe v11) (coe v2) (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v10 of
                    (:) v11 v12
                      -> case coe v1 of
                           (:) v13 v14
                             -> case coe v14 of
                                  (:) v15 v16
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46
                                         (coe
                                            du_'43''43''8314''691'_398 (coe v12) (coe v16) (coe v2)
                                            (coe v8))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v5) (coe v2))
             (coe
                du_'43''43''8314''691'_398 (coe v0) (coe v5) (coe v2) (coe v7))
             (coe
                du_'43''43''8314''691'_398 (coe v5) (coe v1) (coe v2) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.++⁺
d_'43''43''8314'_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_'43''43''8314'_422 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7
  = du_'43''43''8314'_422 v2 v3 v4 v6 v7
du_'43''43''8314'_422 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_'43''43''8314'_422 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v2))
      (coe
         du_'43''43''8314''691'_398 (coe v0) (coe v1) (coe v2) (coe v3))
      (coe du_'43''43''8314''737'_382 (coe v1) (coe v4))
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.zoom
d_zoom_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_zoom_436 ~v0 ~v1 v2 v3 v4 v5 v6 = du_zoom_436 v2 v3 v4 v5 v6
du_zoom_436 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_zoom_436 v0 v1 v2 v3 v4
  = coe
      du_'43''43''8314''737'_382 (coe v0)
      (coe
         du_'43''43''8314''691'_398 (coe v2) (coe v3) (coe v1) (coe v4))
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.inject
d_inject_452 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_inject_452 ~v0 ~v1 v2 v3 ~v4 v5 v6 v7 v8
  = du_inject_452 v2 v3 v5 v6 v7 v8
du_inject_452 ::
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_inject_452 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
      (coe
         du_'43''43''8314''737'_382 (coe v1)
         (coe
            MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
            v5))
      (coe
         du_'43''43''8314''691'_398 (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3))
         (coe v4))
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.shift
d_shift_466 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_shift_466 ~v0 ~v1 v2 v3 v4 = du_shift_466 v2 v3 v4
du_shift_466 ::
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_shift_466 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
      (:) v3 v4
        -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (\ v5 v6 v7 ->
                coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v0))
                      (coe v2))))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4) (coe v2))))
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                   (\ v5 v6 v7 v8 v9 ->
                      coe
                        MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                        v5 v6 v8 v9))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                         (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v0))
                         (coe v2))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4) (coe v2))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4) (coe v2))))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (\ v5 v6 v7 v8 v9 ->
                         coe
                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                           v5 v6 v8 v9))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4) (coe v2))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4) (coe v2))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4) (coe v2))))
                   (let v5
                          = \ v5 ->
                              coe
                                MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50 in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                            (coe v5))
                         (coe
                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                               (coe
                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                                  (coe v2))))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46
                      (coe
                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                   (coe du_shift_466 (coe v0) (coe v4) (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.drop-mid-≡
d_drop'45'mid'45''8801'_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_drop'45'mid'45''8801'_494 ~v0 ~v1 ~v2 v3 v4 v5 v6 ~v7
  = du_drop'45'mid'45''8801'_494 v3 v4 v5 v6
du_drop'45'mid'45''8801'_494 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_drop'45'mid'45''8801'_494 v0 v1 v2 v3
  = case coe v0 of
      []
        -> case coe v1 of
             []
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
             (:) v4 v5 -> coe du_shift_466 (coe v4) (coe v5) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v4 v5
        -> case coe v1 of
             []
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'sym_68
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                       (coe
                          MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v5)
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v4))
                             (coe v2))))
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v2))
                    (coe du_shift_466 (coe v4) (coe v5) (coe v2))
             (:) v6 v7
               -> let v8
                        = coe
                            MAlonzo.Code.Data.List.Properties.du_'8759''45'injective_48 in
                  coe
                    (coe
                       seq (coe v8)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                          (coe
                             du_drop'45'mid'45''8801'_494 (coe v5) (coe v7) (coe v2) (coe v3))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.drop-mid
d_drop'45'mid_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_drop'45'mid_536 v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_drop'45'mid_536 v0 v2 v3 v4 v5 v6 v7
du_drop'45'mid_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_drop'45'mid_536 v0 v1 v2 v3 v4 v5 v6
  = coe
      du_drop'45'mid'8242'_562 (coe v0)
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
            (coe v4)))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
            (coe v5)))
      (coe v6) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5)
-- Data.List.Relation.Binary.Permutation.Propositional.Properties._.drop-mid′
d_drop'45'mid'8242'_562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_drop'45'mid'8242'_562 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 v10
                        v11 v12 v13 v14 v15 v16 v17 ~v18 ~v19
  = du_drop'45'mid'8242'_562 v8 v10 v11 v12 v13 v14 v15 v16 v17
du_drop'45'mid'8242'_562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_drop'45'mid'8242'_562 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
        -> coe
             du_drop'45'mid'45''8801'_494 (coe v5) (coe v6) (coe v7) (coe v8)
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40 v12
        -> case coe v1 of
             (:) v13 v14
               -> case coe v5 of
                    []
                      -> case coe v6 of
                           [] -> coe v12
                           (:) v15 v16
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v16)
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                        (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v13))
                                        (coe v8)))
                                  v12 (coe du_shift_466 (coe v13) (coe v16) (coe v8))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    (:) v15 v16
                      -> case coe v6 of
                           []
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v16)
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                        (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v13))
                                        (coe v7)))
                                  (coe
                                     MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'sym_68
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v16)
                                        (coe
                                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                           (coe
                                              MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                                              (coe v13))
                                           (coe v7)))
                                     (coe
                                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v13)
                                           (coe v16))
                                        (coe v7))
                                     (coe du_shift_466 (coe v13) (coe v16) (coe v7)))
                                  v12
                           (:) v17 v18
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                  (coe
                                     du_drop'45'mid_536 (coe v0) (coe v4) (coe v16) (coe v18)
                                     (coe v7) (coe v8) (coe v12))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46 v13
        -> case coe v1 of
             (:) v14 v15
               -> case coe v15 of
                    (:) v16 v17
                      -> case coe v2 of
                           (:) v18 v19
                             -> case coe v19 of
                                  (:) v20 v21
                                    -> case coe v5 of
                                         []
                                           -> case coe v6 of
                                                []
                                                  -> coe
                                                       MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                       v13
                                                (:) v22 v23
                                                  -> case coe v23 of
                                                       []
                                                         -> let v24
                                                                  = coe
                                                                      MAlonzo.Code.Data.List.Properties.du_'8759''45'injective_48 in
                                                            coe
                                                              (coe
                                                                 seq (coe v24)
                                                                 (coe
                                                                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                                    v13))
                                                       (:) v24 v25
                                                         -> coe
                                                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48
                                                                 (coe
                                                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                    (coe v25)
                                                                    (coe
                                                                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                       (coe
                                                                          MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                                                                          (coe v14))
                                                                       (coe v8)))
                                                                 v13
                                                                 (coe
                                                                    du_shift_466 (coe v14) (coe v25)
                                                                    (coe v8)))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         (:) v22 v23
                                           -> case coe v23 of
                                                []
                                                  -> case coe v6 of
                                                       []
                                                         -> coe
                                                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                              v13
                                                       (:) v24 v25
                                                         -> case coe v25 of
                                                              []
                                                                -> coe
                                                                     MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                                     v13
                                                              (:) v26 v27
                                                                -> coe
                                                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                                                     (\ v28 v29 v30 ->
                                                                        coe
                                                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36
                                                                          v30)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe v14) (coe v17))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe v16)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe v14)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                              (coe v27) (coe v8))))
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                                                           (\ v28 v29 v30 v31 v32 ->
                                                                              coe
                                                                                MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                                                                                v28 v29 v31 v32))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe v14) (coe v17))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe v14)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                              (coe v27)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe v16)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                    (coe v23)
                                                                                    (coe v8)))))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe v16)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe v14)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                 (coe v27)
                                                                                 (coe v8))))
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                                                              (\ v28 v29 v30 v31
                                                                                 v32 ->
                                                                                 coe
                                                                                   MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                                                                                   v28 v29 v31 v32))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe v14)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                 (coe v27)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe v16)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                       (coe v23)
                                                                                       (coe v8)))))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe v14)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe v16)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                    (coe v27)
                                                                                    (coe v8))))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe v16)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe v14)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                    (coe v27)
                                                                                    (coe v8))))
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                                                                 (\ v28 v29 v30 v31
                                                                                    v32 ->
                                                                                    coe
                                                                                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                                                                                      v28 v29 v31
                                                                                      v32))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe v14)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe v16)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                       (coe v27)
                                                                                       (coe v8))))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe v16)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe v14)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                       (coe v27)
                                                                                       (coe v8))))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe v16)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe v14)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                       (coe v27)
                                                                                       (coe v8))))
                                                                              (let v28
                                                                                     = \ v28 ->
                                                                                         coe
                                                                                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50 in
                                                                               coe
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                                                    (coe
                                                                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                                                                       (coe v28))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe v16)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe v14)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                             (coe
                                                                                                v27)
                                                                                             (coe
                                                                                                v8))))))
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36)))
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                                              (coe
                                                                                 du_shift_466
                                                                                 (coe v16) (coe v27)
                                                                                 (coe v8))))
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                                           v13))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                (:) v24 v25
                                                  -> case coe v6 of
                                                       []
                                                         -> coe
                                                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48
                                                                 (coe
                                                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                    (coe v25)
                                                                    (coe
                                                                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                       (coe
                                                                          MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                                                                          (coe v16))
                                                                       (coe v7)))
                                                                 (coe
                                                                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'sym_68
                                                                    (coe
                                                                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                       (coe v25)
                                                                       (coe
                                                                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                          (coe
                                                                             MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                                                                             (coe v16))
                                                                          (coe v7)))
                                                                    (coe
                                                                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe v16) (coe v25))
                                                                       (coe v7))
                                                                    (coe
                                                                       du_shift_466 (coe v16)
                                                                       (coe v25) (coe v7)))
                                                                 v13)
                                                       (:) v26 v27
                                                         -> case coe v27 of
                                                              []
                                                                -> coe
                                                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                                                     (\ v28 v29 v30 ->
                                                                        coe
                                                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36
                                                                          v30)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe v14)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe v16)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                              (coe v25) (coe v7))))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe v16) (coe v21))
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                                                           (\ v28 v29 v30 v31 v32 ->
                                                                              coe
                                                                                MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                                                                                v28 v29 v31 v32))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe v14)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe v16)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                 (coe v25)
                                                                                 (coe v7))))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe v16)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe v14)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                 (coe v25)
                                                                                 (coe v7))))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe v16) (coe v21))
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10216'_418
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                                                              (\ v28 v29 v30 v31
                                                                                 v32 ->
                                                                                 coe
                                                                                   MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                                                                                   v28 v29 v31 v32))
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'sym_68)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe v16)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe v14)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                    (coe v25)
                                                                                    (coe v7))))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe v16)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                 (coe v25)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe v14)
                                                                                    (coe
                                                                                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                       (coe v27)
                                                                                       (coe v7)))))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe v16) (coe v21))
                                                                           (coe
                                                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                                                                 (\ v28 v29 v30 v31
                                                                                    v32 ->
                                                                                    coe
                                                                                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                                                                                      v28 v29 v31
                                                                                      v32))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe v16)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                    (coe v25)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe v14)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                          (coe v27)
                                                                                          (coe
                                                                                             v7)))))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe v16)
                                                                                 (coe v21))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe v16)
                                                                                 (coe v21))
                                                                              (let v28
                                                                                     = \ v28 ->
                                                                                         coe
                                                                                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50 in
                                                                               coe
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                                                    (coe
                                                                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                                                                       (coe v28))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe v16)
                                                                                       (coe v21))))
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                                                 v13))
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                                              (coe
                                                                                 du_shift_466
                                                                                 (coe v14) (coe v25)
                                                                                 (coe v7))))
                                                                        (coe
                                                                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36)))
                                                              (:) v28 v29
                                                                -> coe
                                                                     MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46
                                                                     (coe
                                                                        du_drop'45'mid_536 (coe v0)
                                                                        (coe v4) (coe v25) (coe v29)
                                                                        (coe v7) (coe v8) (coe v13))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48 v10 v12 v13
        -> let v14
                 = coe
                     MAlonzo.Code.Data.List.Membership.Setoid.Properties.du_'8712''45''8707''43''43'_926
                     (coe
                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
                     (coe v10)
                     (coe
                        du_Any'45'resp'45''8621'_140
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v5)
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32
                              (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v4))
                              (coe v7)))
                        (coe v10) (coe v12)
                        (coe
                           MAlonzo.Code.Data.List.Membership.Propositional.Properties.du_'8712''45'insert_214
                           (coe v4) (coe v5))) in
           coe
             (case coe v14 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                  -> case coe v16 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                         -> case coe v18 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                -> let v21
                                         = seq
                                             (coe v20)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                (coe v15)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v17) erased)) in
                                   coe
                                     (case coe v21 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                          -> case coe v23 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                 -> coe
                                                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48
                                                      (coe
                                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                         (coe v22) (coe v24))
                                                      (coe
                                                         du_drop'45'mid_536 (coe v0) (coe v4)
                                                         (coe v5) (coe v22) (coe v7) (coe v24)
                                                         (coe v12))
                                                      (coe
                                                         du_drop'45'mid_536 (coe v0) (coe v4)
                                                         (coe v22) (coe v6) (coe v24) (coe v8)
                                                         (coe v13))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.++-identityˡ
d_'43''43''45'identity'737'_720 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_'43''43''45'identity'737'_720 ~v0 ~v1 ~v2
  = du_'43''43''45'identity'737'_720
du_'43''43''45'identity'737'_720 ::
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_'43''43''45'identity'737'_720
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.++-identityʳ
d_'43''43''45'identity'691'_724 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_'43''43''45'identity'691'_724 ~v0 ~v1 ~v2
  = du_'43''43''45'identity'691'_724
du_'43''43''45'identity'691'_724 ::
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_'43''43''45'identity'691'_724
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'reflexive_62
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.++-identity
d_'43''43''45'identity_728 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''43''45'identity_728 ~v0 ~v1 = du_'43''43''45'identity_728
du_'43''43''45'identity_728 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'43''43''45'identity_728
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 -> coe du_'43''43''45'identity'737'_720)
      (\ v0 -> coe du_'43''43''45'identity'691'_724)
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.++-assoc
d_'43''43''45'assoc_730 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_'43''43''45'assoc_730 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'43''43''45'assoc_730
du_'43''43''45'assoc_730 ::
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_'43''43''45'assoc_730
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'reflexive_62
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.++-comm
d_'43''43''45'comm_738 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_'43''43''45'comm_738 ~v0 ~v1 v2 v3
  = du_'43''43''45'comm_738 v2 v3
du_'43''43''45'comm_738 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_'43''43''45'comm_738 v0 v1
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'sym_68
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v0))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v1))
             (coe du_'43''43''45'identity'691'_724)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (\ v4 v5 v6 ->
                coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3) (coe v1)))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v0))
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                   (\ v4 v5 v6 v7 v8 ->
                      coe
                        MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                        v4 v5 v7 v8))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3) (coe v1)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v3)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v0))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10216'_418
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (\ v4 v5 v6 v7 v8 ->
                         coe
                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                           v4 v5 v7 v8))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'sym_68)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v3)))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v0))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v0))
                   (let v4
                          = \ v4 ->
                              coe
                                MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50 in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                            (coe v4))
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v0))))
                   (coe du_shift_466 (coe v2) (coe v1) (coe v3)))
                (coe
                   MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                   (coe du_'43''43''45'comm_738 (coe v3) (coe v1))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.++-isMagma
d_'43''43''45'isMagma_752 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'43''43''45'isMagma_752 ~v0 ~v1 = du_'43''43''45'isMagma_752
du_'43''43''45'isMagma_752 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'43''43''45'isMagma_752
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'isEquivalence_94)
      (\ v0 v1 v2 v3 v4 v5 -> coe du_'43''43''8314'_422 v0 v1 v2 v4 v5)
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.++-isSemigroup
d_'43''43''45'isSemigroup_754 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'43''43''45'isSemigroup_754 ~v0 ~v1
  = du_'43''43''45'isSemigroup_754
du_'43''43''45'isSemigroup_754 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_'43''43''45'isSemigroup_754
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_9889
      (coe du_'43''43''45'isMagma_752)
      (\ v0 v1 v2 -> coe du_'43''43''45'assoc_730)
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.++-isMonoid
d_'43''43''45'isMonoid_756 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'43''43''45'isMonoid_756 ~v0 ~v1 = du_'43''43''45'isMonoid_756
du_'43''43''45'isMonoid_756 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_'43''43''45'isMonoid_756
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15345
      (coe du_'43''43''45'isSemigroup_754)
      (coe du_'43''43''45'identity_728)
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.++-isCommutativeMonoid
d_'43''43''45'isCommutativeMonoid_758 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'43''43''45'isCommutativeMonoid_758 ~v0 ~v1
  = du_'43''43''45'isCommutativeMonoid_758
du_'43''43''45'isCommutativeMonoid_758 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'43''43''45'isCommutativeMonoid_758
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17167
      (coe du_'43''43''45'isMonoid_756) (coe du_'43''43''45'comm_738)
-- Data.List.Relation.Binary.Permutation.Propositional.Properties._.++-magma
d_'43''43''45'magma_768 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_'43''43''45'magma_768 ~v0 ~v1 = du_'43''43''45'magma_768
du_'43''43''45'magma_768 :: MAlonzo.Code.Algebra.Bundles.T_Magma_72
du_'43''43''45'magma_768
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1323
      (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
      (coe du_'43''43''45'isMagma_752)
-- Data.List.Relation.Binary.Permutation.Propositional.Properties._.++-semigroup
d_'43''43''45'semigroup_770 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_'43''43''45'semigroup_770 ~v0 ~v1 = du_'43''43''45'semigroup_770
du_'43''43''45'semigroup_770 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
du_'43''43''45'semigroup_770
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9837
      (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
      (coe du_'43''43''45'isSemigroup_754)
-- Data.List.Relation.Binary.Permutation.Propositional.Properties._.++-monoid
d_'43''43''45'monoid_772 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_'43''43''45'monoid_772 ~v0 ~v1 = du_'43''43''45'monoid_772
du_'43''43''45'monoid_772 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
du_'43''43''45'monoid_772
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16201
      (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe du_'43''43''45'isMonoid_756)
-- Data.List.Relation.Binary.Permutation.Propositional.Properties._.++-commutativeMonoid
d_'43''43''45'commutativeMonoid_774 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'43''43''45'commutativeMonoid_774 ~v0 ~v1
  = du_'43''43''45'commutativeMonoid_774
du_'43''43''45'commutativeMonoid_774 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
du_'43''43''45'commutativeMonoid_774
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17975
      (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe du_'43''43''45'isCommutativeMonoid_758)
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.shifts
d_shifts_782 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_shifts_782 ~v0 ~v1 v2 v3 v4 = du_shifts_782 v2 v3 v4
du_shifts_782 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_shifts_782 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0)
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v2)))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v2)))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10216'_418
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (\ v3 v4 v5 v6 v7 ->
               coe
                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                 v3 v4 v6 v7))
         (coe
            MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'sym_68)
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0)
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v2)))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v1))
            (coe v2))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v2)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (\ v3 v4 v5 v6 v7 ->
                  coe
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                    v3 v4 v6 v7))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v1))
               (coe v2))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v0))
               (coe v2))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v2)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (\ v3 v4 v5 v6 v7 ->
                     coe
                       MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                       v3 v4 v6 v7))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v0))
                  (coe v2))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v2)))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v2)))
               (let v3
                      = \ v3 ->
                          coe
                            MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50 in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v3))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v2)))))
               (coe du_'43''43''45'assoc_730))
            (coe
               du_'43''43''8314''691'_398
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v0))
               (coe v2) (coe du_'43''43''45'comm_738 (coe v0) (coe v1))))
         (coe du_'43''43''45'assoc_730))
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.drop-∷
d_drop'45''8759'_800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_drop'45''8759'_800 v0 ~v1 v2 v3 v4
  = du_drop'45''8759'_800 v0 v2 v3 v4
du_drop'45''8759'_800 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_drop'45''8759'_800 v0 v1 v2 v3
  = coe
      du_drop'45'mid_536 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v2)
      (coe v3)
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.∷↭∷ʳ
d_'8759''8621''8759''691'_806 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_'8759''8621''8759''691'_806 ~v0 ~v1 v2 v3
  = du_'8759''8621''8759''691'_806 v2 v3
du_'8759''8621''8759''691'_806 ::
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_'8759''8621''8759''691'_806 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'sym_68
      (coe
         MAlonzo.Code.Data.List.Base.du__'8759''691'__448 (coe v1) (coe v0))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v4)
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
            (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v0)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (\ v2 v3 v4 v5 v6 ->
                  coe
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                    v2 v3 v5 v6))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
               (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v0)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v2 v3 v4 v5 v6 -> v6)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1))
               (let v2
                      = \ v2 ->
                          coe
                            MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50 in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v2))
                     (coe
                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1))))
               erased)
            (coe
               du_shift_466 (coe v0) (coe v1)
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.++↭ʳ++
d_'43''43''8621''691''43''43'_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_'43''43''8621''691''43''43'_820 ~v0 ~v1 v2 v3
  = du_'43''43''8621''691''43''43'_820 v2 v3
du_'43''43''8621''691''43''43'_820 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_'43''43''8621''691''43''43'_820 v0 v1
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v1))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v2))
                   (coe v1)))
             (coe
                MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'sym_68
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v2))
                      (coe v1)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0) (coe v1))
                (coe du_shift_466 (coe v2) (coe v3) (coe v1)))
             (coe
                du_'43''43''8621''691''43''43'_820 (coe v3)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.↭-reverse
d_'8621''45'reverse_832 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_'8621''45'reverse_832 ~v0 ~v1 v2 = du_'8621''45'reverse_832 v2
du_'8621''45'reverse_832 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_'8621''45'reverse_832 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50
      (:) v1 v2
        -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (\ v3 v4 v5 ->
                coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
             (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v0) v0
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                (\ v3 v4 v5 v6 v7 -> v7)
                (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v0)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'8759''691'__448
                   (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v2) (coe v1))
                v0
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10216'_418
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (\ v3 v4 v5 v6 v7 ->
                         coe
                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                           v3 v4 v6 v7))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'sym_68)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'8759''691'__448
                      (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v2) (coe v1))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                      (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v2))
                   v0
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                         (\ v3 v4 v5 v6 v7 ->
                            coe
                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                              v3 v4 v6 v7))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                         (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v2))
                      v0 v0
                      (let v3
                             = \ v3 ->
                                 coe
                                   MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50 in
                       coe
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                               (coe v3))
                            (coe v0)))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                         (coe du_'8621''45'reverse_832 (coe v2))))
                   (coe
                      du_'8759''8621''8759''691'_806 (coe v1)
                      (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v2)))
                erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties._.merge-↭
d_merge'45''8621'_858 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_merge'45''8621'_858 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_merge'45''8621'_858 v4 v5 v6
du_merge'45''8621'_858 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_merge'45''8621'_858 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50)
      (:) v3 v4
        -> case coe v2 of
             []
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'sym_68
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v2))
                    (coe
                       MAlonzo.Code.Data.List.Base.du_merge_192 (coe v0) (coe v1)
                       (coe v2))
                    (coe du_'43''43''45'identity'691'_724)
             (:) v5 v6
               -> let v7
                        = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                            (coe v0 v3 v5) in
                  coe
                    (let v8 = coe du_merge'45''8621'_858 (coe v0) (coe v4) (coe v2) in
                     coe
                       (let v9 = coe du_merge'45''8621'_858 (coe v0) (coe v1) (coe v6) in
                        coe
                          (if coe v7
                             then coe
                                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                    v8
                             else coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                    (\ v10 v11 v12 ->
                                       coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36
                                         v12)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_merge_192 (coe v0) (coe v1)
                                          (coe v6)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                                          (coe v2)))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                          (\ v10 v11 v12 v13 v14 ->
                                             coe
                                               MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                                               v10 v11 v13 v14))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                          (coe
                                             MAlonzo.Code.Data.List.Base.du_merge_192 (coe v0)
                                             (coe v1) (coe v6)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                             (coe
                                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                (coe v4) (coe v6))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                          (coe
                                             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                                             (coe v2)))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10216'_418
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                             (\ v10 v11 v12 v13 v14 ->
                                                coe
                                                  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
                                                  v10 v11 v13 v14))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'sym_68)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v5)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe v3)
                                                (coe
                                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                   (coe v4) (coe v6))))
                                          (coe
                                             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
                                             (coe v2))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                             (coe
                                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                (coe v4) (coe v2)))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                             (\ v10 v11 v12 v13 v14 -> v14)
                                             (coe
                                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                (coe v1) (coe v2))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe v3)
                                                (coe
                                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                   (coe v4) (coe v2)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe v3)
                                                (coe
                                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                   (coe v4) (coe v2)))
                                             (let v10
                                                    = \ v10 ->
                                                        coe
                                                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'refl_50 in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                   (coe
                                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                                      (coe v10))
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe v3)
                                                      (coe
                                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                         (coe v4) (coe v2)))))
                                             erased)
                                          (coe du_shift_466 (coe v5) (coe v1) (coe v6)))
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                          v9)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.filter-↭
d_filter'45''8621'_910 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_filter'45''8621'_910 ~v0 ~v1 v2 v3 ~v4 ~v5 v6 v7
  = du_filter'45''8621'_910 v2 v3 v6 v7
du_filter'45''8621'_910 ::
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_filter'45''8621'_910 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v1 of
                    (:) v10 v11
                      -> let v12 = coe v2 v8 in
                         coe
                           (case coe v12 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                -> if coe v13
                                     then coe
                                            seq (coe v14)
                                            (coe
                                               MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                               (coe
                                                  du_filter'45''8621'_910 (coe v9) (coe v11)
                                                  (coe v2) (coe v7)))
                                     else coe
                                            seq (coe v14)
                                            (coe
                                               du_filter'45''8621'_910 (coe v9) (coe v11) (coe v2)
                                               (coe v7))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v10 of
                    (:) v11 v12
                      -> case coe v1 of
                           (:) v13 v14
                             -> case coe v14 of
                                  (:) v15 v16
                                    -> let v17 = coe v2 v9 in
                                       coe
                                         (let v18 = coe v2 v11 in
                                          coe
                                            (case coe v17 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                 -> if coe v19
                                                      then coe
                                                             seq (coe v20)
                                                             (case coe v18 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                  -> if coe v21
                                                                       then coe
                                                                              seq (coe v22)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46
                                                                                 (coe
                                                                                    du_filter'45''8621'_910
                                                                                    (coe v12)
                                                                                    (coe v16)
                                                                                    (coe v2)
                                                                                    (coe v8)))
                                                                       else coe
                                                                              seq (coe v22)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                                                 (coe
                                                                                    du_filter'45''8621'_910
                                                                                    (coe v12)
                                                                                    (coe v16)
                                                                                    (coe v2)
                                                                                    (coe v8)))
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      else coe
                                                             seq (coe v20)
                                                             (case coe v18 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                  -> if coe v21
                                                                       then coe
                                                                              seq (coe v22)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                                                 (coe
                                                                                    du_filter'45''8621'_910
                                                                                    (coe v12)
                                                                                    (coe v16)
                                                                                    (coe v2)
                                                                                    (coe v8)))
                                                                       else coe
                                                                              seq (coe v22)
                                                                              (coe
                                                                                 du_filter'45''8621'_910
                                                                                 (coe v12) (coe v16)
                                                                                 (coe v2) (coe v8))
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.du_'8621''45'trans_84
             (coe MAlonzo.Code.Data.List.Base.du_filter_648 (coe v2) (coe v0))
             (coe MAlonzo.Code.Data.List.Base.du_filter_648 (coe v2) (coe v5))
             (coe du_filter'45''8621'_910 (coe v0) (coe v5) (coe v2) (coe v7))
             (coe du_filter'45''8621'_910 (coe v5) (coe v1) (coe v2) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.catMaybes-↭
d_catMaybes'45''8621'_1022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [Maybe AgdaAny] ->
  [Maybe AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_catMaybes'45''8621'_1022 ~v0 ~v1 v2 v3 v4
  = du_catMaybes'45''8621'_1022 v2 v3 v4
du_catMaybes'45''8621'_1022 ::
  [Maybe AgdaAny] ->
  [Maybe AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_catMaybes'45''8621'_1022 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_refl_36
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40 v6
        -> case coe v0 of
             (:) v7 v8
               -> case coe v1 of
                    (:) v9 v10
                      -> case coe v7 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                  (coe du_catMaybes'45''8621'_1022 (coe v8) (coe v10) (coe v6))
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                             -> coe du_catMaybes'45''8621'_1022 (coe v8) (coe v10) (coe v6)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v9 of
                    (:) v10 v11
                      -> case coe v1 of
                           (:) v12 v13
                             -> case coe v13 of
                                  (:) v14 v15
                                    -> case coe v8 of
                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                           -> case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                                  -> coe
                                                       MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_swap_46
                                                       (coe
                                                          du_catMaybes'45''8621'_1022 (coe v11)
                                                          (coe v15) (coe v7))
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> coe
                                                       MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                       (coe
                                                          du_catMaybes'45''8621'_1022 (coe v11)
                                                          (coe v15) (coe v7))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                           -> case coe v10 of
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                  -> coe
                                                       MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_prep_40
                                                       (coe
                                                          du_catMaybes'45''8621'_1022 (coe v11)
                                                          (coe v15) (coe v7))
                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                  -> coe
                                                       du_catMaybes'45''8621'_1022 (coe v11)
                                                       (coe v15) (coe v7)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.C_trans_48
             (coe MAlonzo.Code.Data.List.Base.du_catMaybes_256 v4)
             (coe du_catMaybes'45''8621'_1022 (coe v0) (coe v4) (coe v6))
             (coe du_catMaybes'45''8621'_1022 (coe v4) (coe v1) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.mapMaybe-↭
d_mapMaybe'45''8621'_1052 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> Maybe AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
d_mapMaybe'45''8621'_1052 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_mapMaybe'45''8621'_1052 v4 v5 v6 v7
du_mapMaybe'45''8621'_1052 ::
  [AgdaAny] ->
  [AgdaAny] ->
  (AgdaAny -> Maybe AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34
du_mapMaybe'45''8621'_1052 v0 v1 v2 v3
  = coe
      du_catMaybes'45''8621'_1022
      (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v2) (coe v0))
      (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v2) (coe v1))
      (coe du_map'8314'_294 (coe v2) (coe v0) (coe v1) (coe v3))
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.sum-↭
d_sum'45''8621'_1056 ::
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sum'45''8621'_1056 = erased
-- Data.List.Relation.Binary.Permutation.Propositional.Properties.product-↭
d_product'45''8621'_1058 ::
  [Integer] ->
  [Integer] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional.T__'8621'__34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_product'45''8621'_1058 = erased
