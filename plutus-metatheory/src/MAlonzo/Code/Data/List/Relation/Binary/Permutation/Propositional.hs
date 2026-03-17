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

module MAlonzo.Code.Data.List.Relation.Binary.Permutation.Propositional where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous
import qualified MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Data.List.Relation.Binary.Permutation.Propositional._↭_
d__'8621'__34 a0 a1 a2 a3 = ()
data T__'8621'__34
  = C_refl_36 | C_prep_40 T__'8621'__34 | C_swap_46 T__'8621'__34 |
    C_trans_48 [AgdaAny] T__'8621'__34 T__'8621'__34
-- Data.List.Relation.Binary.Permutation.Propositional.↭-refl
d_'8621''45'refl_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> T__'8621'__34
d_'8621''45'refl_50 ~v0 ~v1 ~v2 = du_'8621''45'refl_50
du_'8621''45'refl_50 :: T__'8621'__34
du_'8621''45'refl_50 = coe C_refl_36
-- Data.List.Relation.Binary.Permutation.Propositional.↭-prep
d_'8621''45'prep_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] -> [AgdaAny] -> AgdaAny -> T__'8621'__34 -> T__'8621'__34
d_'8621''45'prep_54 ~v0 ~v1 ~v2 ~v3 = du_'8621''45'prep_54
du_'8621''45'prep_54 :: AgdaAny -> T__'8621'__34 -> T__'8621'__34
du_'8621''45'prep_54 v0 v1 = coe C_prep_40 v1
-- Data.List.Relation.Binary.Permutation.Propositional.↭-swap
d_'8621''45'swap_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] -> AgdaAny -> AgdaAny -> T__'8621'__34 -> T__'8621'__34
d_'8621''45'swap_60 ~v0 ~v1 ~v2 ~v3 = du_'8621''45'swap_60
du_'8621''45'swap_60 ::
  AgdaAny -> AgdaAny -> T__'8621'__34 -> T__'8621'__34
du_'8621''45'swap_60 v0 v1 v2 = coe C_swap_46 v2
-- Data.List.Relation.Binary.Permutation.Propositional.↭-reflexive
d_'8621''45'reflexive_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'8621'__34
d_'8621''45'reflexive_62 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'8621''45'reflexive_62
du_'8621''45'reflexive_62 :: T__'8621'__34
du_'8621''45'reflexive_62 = coe du_'8621''45'refl_50
-- Data.List.Relation.Binary.Permutation.Propositional.↭-reflexive-≋
d_'8621''45'reflexive'45''8779'_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  T__'8621'__34
d_'8621''45'reflexive'45''8779'_64 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'8621''45'reflexive'45''8779'_64
du_'8621''45'reflexive'45''8779'_64 :: T__'8621'__34
du_'8621''45'reflexive'45''8779'_64 = coe du_'8621''45'reflexive_62
-- Data.List.Relation.Binary.Permutation.Propositional.↭-sym
d_'8621''45'sym_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> T__'8621'__34 -> T__'8621'__34
d_'8621''45'sym_68 ~v0 ~v1 v2 v3 v4 = du_'8621''45'sym_68 v2 v3 v4
du_'8621''45'sym_68 ::
  [AgdaAny] -> [AgdaAny] -> T__'8621'__34 -> T__'8621'__34
du_'8621''45'sym_68 v0 v1 v2
  = case coe v2 of
      C_refl_36 -> coe C_refl_36
      C_prep_40 v6
        -> case coe v0 of
             (:) v7 v8
               -> case coe v1 of
                    (:) v9 v10
                      -> coe
                           C_prep_40 (coe du_'8621''45'sym_68 (coe v8) (coe v10) (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_swap_46 v7
        -> case coe v0 of
             (:) v8 v9
               -> case coe v9 of
                    (:) v10 v11
                      -> case coe v1 of
                           (:) v12 v13
                             -> case coe v13 of
                                  (:) v14 v15
                                    -> coe
                                         C_swap_46
                                         (coe du_'8621''45'sym_68 (coe v11) (coe v15) (coe v7))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_trans_48 v4 v6 v7
        -> coe
             C_trans_48 v4 (coe du_'8621''45'sym_68 (coe v4) (coe v1) (coe v7))
             (coe du_'8621''45'sym_68 (coe v0) (coe v4) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.↭-trans
d_'8621''45'trans_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] -> T__'8621'__34 -> T__'8621'__34 -> T__'8621'__34
d_'8621''45'trans_84 ~v0 ~v1 v2 v3 ~v4 v5 v6
  = du_'8621''45'trans_84 v2 v3 v5 v6
du_'8621''45'trans_84 ::
  [AgdaAny] ->
  [AgdaAny] -> T__'8621'__34 -> T__'8621'__34 -> T__'8621'__34
du_'8621''45'trans_84 v0 v1 v2 v3
  = case coe v2 of
      C_refl_36 -> coe v3
      C_prep_40 v7
        -> let v8
                 = let v8 = coe C_trans_48 v1 (coe C_prep_40 v7) v3 in
                   coe
                     (case coe v3 of
                        C_refl_36 -> coe C_prep_40 v7
                        _ -> coe v8) in
           coe
             (case coe v0 of
                (:) v9 v10
                  -> let v11
                           = let v11 = coe C_trans_48 v1 (coe C_prep_40 v7) v3 in
                             coe
                               (case coe v3 of
                                  C_refl_36 -> coe C_prep_40 v7
                                  _ -> coe v11) in
                     coe
                       (case coe v1 of
                          (:) v12 v13
                            -> let v14 = coe C_trans_48 v1 (coe C_prep_40 v7) v3 in
                               coe
                                 (case coe v3 of
                                    C_refl_36 -> coe C_prep_40 v7
                                    _ -> coe v14)
                          _ -> coe v11)
                _ -> coe v8)
      C_swap_46 v8
        -> let v9
                 = let v9 = coe C_trans_48 v1 (coe C_swap_46 v8) v3 in
                   coe
                     (case coe v3 of
                        C_refl_36 -> coe C_swap_46 v8
                        _ -> coe v9) in
           coe
             (case coe v0 of
                (:) v10 v11
                  -> let v12
                           = let v12 = coe C_trans_48 v1 (coe C_swap_46 v8) v3 in
                             coe
                               (case coe v3 of
                                  C_refl_36 -> coe C_swap_46 v8
                                  _ -> coe v12) in
                     coe
                       (case coe v11 of
                          (:) v13 v14
                            -> let v15
                                     = let v15 = coe C_trans_48 v1 (coe C_swap_46 v8) v3 in
                                       coe
                                         (case coe v3 of
                                            C_refl_36 -> coe C_swap_46 v8
                                            _ -> coe v15) in
                               coe
                                 (case coe v1 of
                                    (:) v16 v17
                                      -> let v18
                                               = let v18
                                                       = coe C_trans_48 v1 (coe C_swap_46 v8) v3 in
                                                 coe
                                                   (case coe v3 of
                                                      C_refl_36 -> coe C_swap_46 v8
                                                      _ -> coe v18) in
                                         coe
                                           (case coe v17 of
                                              (:) v19 v20
                                                -> let v21
                                                         = coe
                                                             C_trans_48 v1 (coe C_swap_46 v8) v3 in
                                                   coe
                                                     (case coe v3 of
                                                        C_refl_36 -> coe C_swap_46 v8
                                                        _ -> coe v21)
                                              _ -> coe v18)
                                    _ -> coe v15)
                          _ -> coe v12)
                _ -> coe v9)
      C_trans_48 v5 v7 v8
        -> let v9 = coe C_trans_48 v1 (coe C_trans_48 v5 v7 v8) v3 in
           coe
             (case coe v3 of
                C_refl_36 -> coe C_trans_48 v5 v7 v8
                _ -> coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.↭-isEquivalence
d_'8621''45'isEquivalence_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8621''45'isEquivalence_94 ~v0 ~v1
  = du_'8621''45'isEquivalence_94
du_'8621''45'isEquivalence_94 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_'8621''45'isEquivalence_94
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (\ v0 -> coe du_'8621''45'refl_50) (coe du_'8621''45'sym_68)
      (\ v0 v1 v2 v3 v4 -> coe du_'8621''45'trans_84 v0 v1 v3 v4)
-- Data.List.Relation.Binary.Permutation.Propositional.↭-setoid
d_'8621''45'setoid_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8621''45'setoid_96 ~v0 ~v1 = du_'8621''45'setoid_96
du_'8621''45'setoid_96 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_'8621''45'setoid_96
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_761
      (coe du_'8621''45'isEquivalence_94)
-- Data.List.Relation.Binary.Permutation.Propositional._.↭ₛ′._↭_
d__'8621'__110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8621'__110 = erased
-- Data.List.Relation.Binary.Permutation.Propositional._.↭⇒↭ₛ′
d_'8621''8658''8621''8347''8242'_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  [AgdaAny] ->
  [AgdaAny] ->
  T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''8658''8621''8347''8242'_228 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'8621''8658''8621''8347''8242'_228 v4 v5 v6 v7
du_'8621''8658''8621''8347''8242'_228 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  [AgdaAny] ->
  [AgdaAny] ->
  T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''8658''8621''8347''8242'_228 v0 v1 v2 v3
  = case coe v3 of
      C_refl_36
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'refl_94
             (coe
                MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_761
                v0)
             (coe v1)
      C_prep_40 v7
        -> case coe v1 of
             (:) v8 v9
               -> case coe v2 of
                    (:) v10 v11
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                           (coe MAlonzo.Code.Relation.Binary.Structures.d_refl_34 v0 v8)
                           (coe
                              du_'8621''8658''8621''8347''8242'_228 (coe v0) (coe v9) (coe v11)
                              (coe v7))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_swap_46 v8
        -> case coe v1 of
             (:) v9 v10
               -> case coe v10 of
                    (:) v11 v12
                      -> case coe v2 of
                           (:) v13 v14
                             -> case coe v14 of
                                  (:) v15 v16
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Structures.d_refl_34 v0 v9)
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Structures.d_refl_34 v0
                                            v11)
                                         (coe
                                            du_'8621''8658''8621''8347''8242'_228 (coe v0) (coe v12)
                                            (coe v16) (coe v8))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_trans_48 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'trans'8242'_162
             (coe
                MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_761
                v0)
             (coe v1) (coe v5) (coe v2)
             (coe
                du_'8621''8658''8621''8347''8242'_228 (coe v0) (coe v1) (coe v5)
                (coe v7))
             (coe
                du_'8621''8658''8621''8347''8242'_228 (coe v0) (coe v5) (coe v2)
                (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.↭ₛ._↭_
d__'8621'__246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> ()
d__'8621'__246 = erased
-- Data.List.Relation.Binary.Permutation.Propositional.↭⇒↭ₛ
d_'8621''8658''8621''8347'_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''8658''8621''8347'_364 ~v0 ~v1 v2 v3
  = du_'8621''8658''8621''8347'_364 v2 v3
du_'8621''8658''8621''8347'_364 ::
  [AgdaAny] ->
  [AgdaAny] ->
  T__'8621'__34 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''8658''8621''8347'_364 v0 v1
  = coe
      du_'8621''8658''8621''8347''8242'_228
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (coe v0) (coe v1)
-- Data.List.Relation.Binary.Permutation.Propositional.↭ₛ⇒↭
d_'8621''8347''8658''8621'_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  T__'8621'__34
d_'8621''8347''8658''8621'_366 ~v0 ~v1 v2 v3 v4
  = du_'8621''8347''8658''8621'_366 v2 v3 v4
du_'8621''8347''8658''8621'_366 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  T__'8621'__34
du_'8621''8347''8658''8621'_366 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v5
        -> coe du_'8621''45'reflexive'45''8779'_64
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    (:) v11 v12
                      -> coe
                           du_'8621''45'prep_54 v9
                           (coe du_'8621''8347''8658''8621'_366 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v9 v10 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v13 of
                    (:) v14 v15
                      -> case coe v1 of
                           (:) v16 v17
                             -> case coe v17 of
                                  (:) v18 v19
                                    -> coe
                                         du_'8621''45'swap_60 v12 v14
                                         (coe
                                            du_'8621''8347''8658''8621'_366 (coe v15) (coe v19)
                                            (coe v11))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v4 v6 v7
        -> coe
             du_'8621''45'trans_84 (coe v0) (coe v4)
             (coe du_'8621''8347''8658''8621'_366 (coe v0) (coe v4) (coe v6))
             (coe du_'8621''8347''8658''8621'_366 (coe v4) (coe v1) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning.Base._IsRelatedTo_
d__IsRelatedTo__382 a0 a1 a2 a3 = ()
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning.Base._∎
d__'8718'_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d__'8718'_384 ~v0 ~v1 = du__'8718'_384
du__'8718'_384 ::
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du__'8718'_384
  = let v0 = coe du_'8621''45'setoid_96 in
    coe
      (let v1
             = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                    (coe v0)) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
               (coe v1))))
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning.Base.begin_
d_begin__386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34
d_begin__386 ~v0 ~v1 = du_begin__386
du_begin__386 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34
du_begin__386
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v0 v1 v2 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v2)
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning.Base.start
d_start_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34
d_start_390 ~v0 ~v1 = du_start_390
du_start_390 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34
du_start_390 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v2
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning.Base.step-≡
d_step'45''8801'_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801'_400 ~v0 ~v1 = du_step'45''8801'_400
du_step'45''8801'_400 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8801'_400
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning.Base.step-≡-∣
d_step'45''8801''45''8739'_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''45''8739'_402 ~v0 ~v1 ~v2 ~v3 v4
  = du_step'45''8801''45''8739'_402 v4
du_step'45''8801''45''8739'_402 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8801''45''8739'_402 v0 = coe v0
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning.Base.step-≡-⟨
d_step'45''8801''45''10216'_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''45''10216'_404 ~v0 ~v1
  = du_step'45''8801''45''10216'_404
du_step'45''8801''45''10216'_404 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8801''45''10216'_404
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning.Base.step-≡-⟩
d_step'45''8801''45''10217'_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''45''10217'_406 ~v0 ~v1
  = du_step'45''8801''45''10217'_406
du_step'45''8801''45''10217'_406 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8801''45''10217'_406
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning.Base.step-≡˘
d_step'45''8801''728'_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''728'_408 ~v0 ~v1 = du_step'45''8801''728'_408
du_step'45''8801''728'_408 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8801''728'_408
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning.Base.stop
d_stop_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_stop_410 ~v0 ~v1 = du_stop_410
du_stop_410 ::
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_stop_410
  = let v0 = coe du_'8621''45'setoid_96 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning.Base.∼-go
d_'8764''45'go_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  T__'8621'__34 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_'8764''45'go_412 ~v0 ~v1 = du_'8764''45'go_412
du_'8764''45'go_412 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  T__'8621'__34 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_'8764''45'go_412
  = let v0 = coe du_'8621''45'setoid_96 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning.Base.≡-go
d_'8801''45'go_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_'8801''45'go_414 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8801''45'go_414 v6
du_'8801''45'go_414 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_'8801''45'go_414 v0 = coe v0
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning._.step-↭
d_step'45''8621'_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8621'_422 ~v0 ~v1 = du_step'45''8621'_422
du_step'45''8621'_422 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8621'_422
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621'_420
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
         (\ v0 v1 v2 v3 v4 -> coe du_'8621''45'trans_84 v0 v1 v3 v4))
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning._.step-↭-⟨
d_step'45''8621''45''10216'_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8621''45''10216'_424 ~v0 ~v1
  = du_step'45''8621''45''10216'_424
du_step'45''8621''45''10216'_424 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8621''45''10216'_424
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10216'_418
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
         (\ v0 v1 v2 v3 v4 -> coe du_'8621''45'trans_84 v0 v1 v3 v4))
      (coe du_'8621''45'sym_68)
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning._.step-↭-⟩
d_step'45''8621''45''10217'_426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8621''45''10217'_426 ~v0 ~v1
  = du_step'45''8621''45''10217'_426
du_step'45''8621''45''10217'_426 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8621''45''10217'_426
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
         (\ v0 v1 v2 v3 v4 -> coe du_'8621''45'trans_84 v0 v1 v3 v4))
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning._.step-↭˘
d_step'45''8621''728'_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8621''728'_428 ~v0 ~v1 = du_step'45''8621''728'_428
du_step'45''8621''728'_428 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8621''728'_428
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''728'_422
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
         (\ v0 v1 v2 v3 v4 -> coe du_'8621''45'trans_84 v0 v1 v3 v4))
      (coe du_'8621''45'sym_68)
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning.step-prep
d_step'45'prep_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45'prep_438 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_step'45'prep_438 v2 v3 v4 v5 v6 v7
du_step'45'prep_438 ::
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45'prep_438 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
      (\ v6 v7 v8 v9 v10 -> coe du_'8621''45'trans_84 v6 v7 v9 v10)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v2))
      (coe v3) (coe du_'8621''45'prep_54 v0 v5) (coe v4)
-- Data.List.Relation.Binary.Permutation.Propositional.PermutationReasoning.step-swap
d_step'45'swap_458 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45'swap_458 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_step'45'swap_458 v2 v3 v4 v5 v6 v7 v8
du_step'45'swap_458 ::
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  T__'8621'__34 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45'swap_458 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
      (\ v7 v8 v9 v10 v11 -> coe du_'8621''45'trans_84 v7 v8 v10 v11)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v2)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v0) (coe v3)))
      (coe v4) (coe du_'8621''45'swap_60 v0 v1 v6) (coe v5)
