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

module MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid
import qualified MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Bundles.Raw
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Data.List.Relation.Binary.Permutation.Setoid.≈._≈_
d__'8776'__20 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__20 = erased
-- Data.List.Relation.Binary.Permutation.Setoid.≈._≉_
d__'8777'__22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__22 = erased
-- Data.List.Relation.Binary.Permutation.Setoid.≈.Carrier
d_Carrier_24 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 -> ()
d_Carrier_24 = erased
-- Data.List.Relation.Binary.Permutation.Setoid.≈.isEquivalence
d_isEquivalence_26 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_26 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)
-- Data.List.Relation.Binary.Permutation.Setoid.≈.isPartialEquivalence
d_isPartialEquivalence_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_28 ~v0 ~v1 v2
  = du_isPartialEquivalence_28 v2
du_isPartialEquivalence_28 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_28 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.≈.partialSetoid
d_partialSetoid_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
d_partialSetoid_30 ~v0 ~v1 v2 = du_partialSetoid_30 v2
du_partialSetoid_30 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_PartialSetoid_10
du_partialSetoid_30 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.du_partialSetoid_70 (coe v0)
-- Data.List.Relation.Binary.Permutation.Setoid.≈.rawSetoid
d_rawSetoid_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.Raw.T_RawSetoid_12
d_rawSetoid_32 = erased
-- Data.List.Relation.Binary.Permutation.Setoid.≈.refl
d_refl_34 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> AgdaAny
d_refl_34 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.≈.reflexive
d_reflexive_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_36 ~v0 ~v1 v2 = du_reflexive_36 v2
du_reflexive_36 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_36 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
      v1
-- Data.List.Relation.Binary.Permutation.Setoid.≈.sym
d_sym_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_38 ~v0 ~v1 v2 = du_sym_38 v2
du_sym_38 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_38 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_36
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.≈.trans
d_trans_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_40 ~v0 ~v1 v2 = du_trans_40 v2
du_trans_40 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_40 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid._._≋_
d__'8779'__44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8779'__44 = erased
-- Data.List.Relation.Binary.Permutation.Setoid._↭_
d__'8621'__56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8621'__56 = erased
-- Data.List.Relation.Binary.Permutation.Setoid.steps
d_steps_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  Integer
d_steps_58 ~v0 ~v1 ~v2 = du_steps_58
du_steps_58 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  Integer
du_steps_58
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.du_steps_152
-- Data.List.Relation.Binary.Permutation.Setoid.↭-reflexive-≋
d_'8621''45'reflexive'45''8779'_60 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''45'reflexive'45''8779'_60 ~v0 ~v1 ~v2
  = du_'8621''45'reflexive'45''8779'_60
du_'8621''45'reflexive'45''8779'_60 ::
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''45'reflexive'45''8779'_60
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42
-- Data.List.Relation.Binary.Permutation.Setoid.↭-trans
d_'8621''45'trans_62 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''45'trans_62 ~v0 ~v1 v2 ~v3 = du_'8621''45'trans_62 v2
du_'8621''45'trans_62 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''45'trans_62 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
      (coe v0)
-- Data.List.Relation.Binary.Permutation.Setoid.↭-prep
d_'8621''45'prep_70 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''45'prep_70 v0 v1 ~v2 ~v3 v4
  = du_'8621''45'prep_70 v0 v1 v4
du_'8621''45'prep_70 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''45'prep_70 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
         v1)
      v2
-- Data.List.Relation.Binary.Permutation.Setoid.↭-swap
d_'8621''45'swap_84 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''45'swap_84 v0 v1 v2 ~v3 ~v4 v5
  = du_'8621''45'swap_84 v0 v1 v2 v5
du_'8621''45'swap_84 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''45'swap_84 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
         v1)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
         v2)
      v3
-- Data.List.Relation.Binary.Permutation.Setoid.↭-reflexive
d_'8621''45'reflexive_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''45'reflexive_92 ~v0 ~v1 v2 v3 ~v4 ~v5
  = du_'8621''45'reflexive_92 v2 v3
du_'8621''45'reflexive_92 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''45'reflexive_92 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
            (coe
               MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
               (coe v0)))
         v1)
-- Data.List.Relation.Binary.Permutation.Setoid.↭-refl
d_'8621''45'refl_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''45'refl_94 ~v0 ~v1 v2 v3 = du_'8621''45'refl_94 v2 v3
du_'8621''45'refl_94 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''45'refl_94 v0 v1
  = coe du_'8621''45'reflexive_92 (coe v0) (coe v1)
-- Data.List.Relation.Binary.Permutation.Setoid.↭-sym
d_'8621''45'sym_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''45'sym_96 ~v0 ~v1 v2 v3 v4 = du_'8621''45'sym_96 v2 v3 v4
du_'8621''45'sym_96 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''45'sym_96 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.du_sym_82
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
      (coe v1) (coe v2)
-- Data.List.Relation.Binary.Permutation.Setoid.↭-transˡ-≋
d_'8621''45'trans'737''45''8779'_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''45'trans'737''45''8779'_98 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_'8621''45'trans'737''45''8779'_98 v2 v3 v4 v5 v6 v7
du_'8621''45'trans'737''45''8779'_98 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''45'trans'737''45''8779'_98 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42
             (let v9
                    = coe
                        MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                        (coe v0) in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                   (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v9))
                   v1 v2 v3 v4 v8))
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v10 v11
        -> case coe v2 of
             (:) v12 v13
               -> case coe v3 of
                    (:) v14 v15
                      -> case coe v4 of
                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v20 v21
                             -> case coe v1 of
                                  (:) v22 v23
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                               (coe v0))
                                            v22 v12 v14 v20 v10)
                                         (coe
                                            du_'8621''45'trans'737''45''8779'_98 (coe v0) (coe v23)
                                            (coe v13) (coe v15) (coe v21) (coe v11))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v12 v13 v14
        -> case coe v2 of
             (:) v15 v16
               -> case coe v16 of
                    (:) v17 v18
                      -> case coe v3 of
                           (:) v19 v20
                             -> case coe v20 of
                                  (:) v21 v22
                                    -> case coe v4 of
                                         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v27 v28
                                           -> case coe v1 of
                                                (:) v29 v30
                                                  -> case coe v28 of
                                                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v35 v36
                                                         -> case coe v30 of
                                                              (:) v37 v38
                                                                -> coe
                                                                     MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                        (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                           (coe v0))
                                                                        v29 v15 v21 v27 v12)
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                        (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                           (coe v0))
                                                                        v37 v17 v19 v35 v13)
                                                                     (coe
                                                                        du_'8621''45'trans'737''45''8779'_98
                                                                        (coe v0) (coe v38) (coe v18)
                                                                        (coe v22) (coe v36)
                                                                        (coe v14))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
             v7
             (coe
                du_'8621''45'trans'737''45''8779'_98 (coe v0) (coe v1) (coe v2)
                (coe v7) (coe v4) (coe v9))
             v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.↭-transʳ-≋
d_'8621''45'trans'691''45''8779'_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''45'trans'691''45''8779'_130 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_'8621''45'trans'691''45''8779'_130 v2 v3 v4 v5 v6 v7
du_'8621''45'trans'691''45''8779'_130 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''45'trans'691''45''8779'_130 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42
             (let v9
                    = coe
                        MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                        (coe v0) in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                   (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v9))
                   v1 v2 v3 v8 v5))
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v10 v11
        -> case coe v1 of
             (:) v12 v13
               -> case coe v2 of
                    (:) v14 v15
                      -> case coe v5 of
                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v20 v21
                             -> case coe v3 of
                                  (:) v22 v23
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                               (coe v0))
                                            v12 v14 v22 v10 v20)
                                         (coe
                                            du_'8621''45'trans'691''45''8779'_130 (coe v0) (coe v13)
                                            (coe v15) (coe v23) (coe v11) (coe v21))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v12 v13 v14
        -> case coe v1 of
             (:) v15 v16
               -> case coe v16 of
                    (:) v17 v18
                      -> case coe v2 of
                           (:) v19 v20
                             -> case coe v20 of
                                  (:) v21 v22
                                    -> case coe v5 of
                                         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v27 v28
                                           -> case coe v3 of
                                                (:) v29 v30
                                                  -> case coe v28 of
                                                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v35 v36
                                                         -> case coe v30 of
                                                              (:) v37 v38
                                                                -> coe
                                                                     MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                        (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                           (coe v0))
                                                                        v15 v21 v37 v12 v35)
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                        (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                           (coe v0))
                                                                        v17 v19 v29 v13 v27)
                                                                     (coe
                                                                        du_'8621''45'trans'691''45''8779'_130
                                                                        (coe v0) (coe v18) (coe v22)
                                                                        (coe v38) (coe v14)
                                                                        (coe v36))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
             v7 v9
             (coe
                du_'8621''45'trans'691''45''8779'_130 (coe v0) (coe v7) (coe v2)
                (coe v3) (coe v10) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.↭-trans′
d_'8621''45'trans'8242'_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''45'trans'8242'_162 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_'8621''45'trans'8242'_162 v2 v3 v4 v5 v6 v7
du_'8621''45'trans'8242'_162 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''45'trans'8242'_162 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v8
        -> coe
             du_'8621''45'trans'737''45''8779'_98 (coe v0) (coe v1) (coe v2)
             (coe v3) (coe v8) (coe v5)
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v10 v11
        -> let v12
                 = let v12
                         = coe
                             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                             v2
                             (coe
                                MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                v10 v11)
                             v5 in
                   coe
                     (case coe v5 of
                        MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v15
                          -> coe
                               du_'8621''45'trans'691''45''8779'_130 (coe v0) (coe v1) (coe v2)
                               (coe v3)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                  v10 v11)
                               (coe v15)
                        _ -> coe v12) in
           coe
             (case coe v1 of
                (:) v13 v14
                  -> let v15
                           = let v15
                                   = coe
                                       MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                                       v2
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                          v10 v11)
                                       v5 in
                             coe
                               (case coe v5 of
                                  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v18
                                    -> coe
                                         du_'8621''45'trans'691''45''8779'_130 (coe v0) (coe v1)
                                         (coe v2) (coe v3)
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                            v10 v11)
                                         (coe v18)
                                  _ -> coe v15) in
                     coe
                       (case coe v2 of
                          (:) v16 v17
                            -> let v18
                                     = coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                                         v2
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                            v10 v11)
                                         v5 in
                               coe
                                 (case coe v5 of
                                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v21
                                      -> coe
                                           du_'8621''45'trans'691''45''8779'_130 (coe v0) (coe v1)
                                           (coe v2) (coe v3)
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                              v10 v11)
                                           (coe v21)
                                    _ -> coe v18)
                          _ -> coe v15)
                _ -> coe v12)
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v12 v13 v14
        -> let v15
                 = let v15
                         = coe
                             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                             v2
                             (coe
                                MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                v12 v13 v14)
                             v5 in
                   coe
                     (case coe v5 of
                        MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v18
                          -> coe
                               du_'8621''45'trans'691''45''8779'_130 (coe v0) (coe v1) (coe v2)
                               (coe v3)
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                  v12 v13 v14)
                               (coe v18)
                        _ -> coe v15) in
           coe
             (case coe v1 of
                (:) v16 v17
                  -> let v18
                           = let v18
                                   = coe
                                       MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                                       v2
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                          v12 v13 v14)
                                       v5 in
                             coe
                               (case coe v5 of
                                  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v21
                                    -> coe
                                         du_'8621''45'trans'691''45''8779'_130 (coe v0) (coe v1)
                                         (coe v2) (coe v3)
                                         (coe
                                            MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                            v12 v13 v14)
                                         (coe v21)
                                  _ -> coe v18) in
                     coe
                       (case coe v17 of
                          (:) v19 v20
                            -> let v21
                                     = let v21
                                             = coe
                                                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                                                 v2
                                                 (coe
                                                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                                    v12 v13 v14)
                                                 v5 in
                                       coe
                                         (case coe v5 of
                                            MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v24
                                              -> coe
                                                   du_'8621''45'trans'691''45''8779'_130 (coe v0)
                                                   (coe v1) (coe v2) (coe v3)
                                                   (coe
                                                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                                      v12 v13 v14)
                                                   (coe v24)
                                            _ -> coe v21) in
                               coe
                                 (case coe v2 of
                                    (:) v22 v23
                                      -> let v24
                                               = let v24
                                                       = coe
                                                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                                                           v2
                                                           (coe
                                                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                                              v12 v13 v14)
                                                           v5 in
                                                 coe
                                                   (case coe v5 of
                                                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v27
                                                        -> coe
                                                             du_'8621''45'trans'691''45''8779'_130
                                                             (coe v0) (coe v1) (coe v2) (coe v3)
                                                             (coe
                                                                MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                                                v12 v13 v14)
                                                             (coe v27)
                                                      _ -> coe v24) in
                                         coe
                                           (case coe v23 of
                                              (:) v25 v26
                                                -> let v27
                                                         = coe
                                                             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                                                             v2
                                                             (coe
                                                                MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                                                v12 v13 v14)
                                                             v5 in
                                                   coe
                                                     (case coe v5 of
                                                        MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v30
                                                          -> coe
                                                               du_'8621''45'trans'691''45''8779'_130
                                                               (coe v0) (coe v1) (coe v2) (coe v3)
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                                                  v12 v13 v14)
                                                               (coe v30)
                                                        _ -> coe v27)
                                              _ -> coe v24)
                                    _ -> coe v21)
                          _ -> coe v18)
                _ -> coe v15)
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v7 v9 v10
        -> let v11
                 = coe
                     MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                     v2
                     (coe
                        MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                        v7 v9 v10)
                     v5 in
           coe
             (case coe v5 of
                MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v14
                  -> coe
                       du_'8621''45'trans'691''45''8779'_130 (coe v0) (coe v1) (coe v2)
                       (coe v3)
                       (coe
                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                          v7 v9 v10)
                       (coe v14)
                _ -> coe v11)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.↭-isEquivalence
d_'8621''45'isEquivalence_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8621''45'isEquivalence_176 ~v0 ~v1 v2
  = du_'8621''45'isEquivalence_176 v2
du_'8621''45'isEquivalence_176 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_'8621''45'isEquivalence_176 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (coe du_'8621''45'refl_94 (coe v0))
      (coe du_'8621''45'sym_96 (coe v0))
      (coe
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
              (coe v2)))
-- Data.List.Relation.Binary.Permutation.Setoid.↭-setoid
d_'8621''45'setoid_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8621''45'setoid_178 ~v0 ~v1 v2 = du_'8621''45'setoid_178 v2
du_'8621''45'setoid_178 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_'8621''45'setoid_178 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_761
      (coe du_'8621''45'isEquivalence_176 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning.Base._IsRelatedTo_
d__IsRelatedTo__184 a0 a1 a2 a3 a4 = ()
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning.Base._∎
d__'8718'_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d__'8718'_186 ~v0 ~v1 v2 = du__'8718'_186 v2
du__'8718'_186 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du__'8718'_186 v0
  = let v1 = coe du_'8621''45'setoid_178 (coe v0) in
    coe
      (let v2
             = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                    (coe v1)) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
               (coe v2))))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning.Base.begin_
d_begin__188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_begin__188 ~v0 ~v1 ~v2 = du_begin__188
du_begin__188 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_begin__188
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v0 v1 v2 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v2)
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning.Base.start
d_start_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_start_192 ~v0 ~v1 ~v2 = du_start_192
du_start_192 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_start_192 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v2
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning.Base.step-≡
d_step'45''8801'_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801'_202 ~v0 ~v1 ~v2 = du_step'45''8801'_202
du_step'45''8801'_202 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8801'_202
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning.Base.step-≡-∣
d_step'45''8801''45''8739'_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''45''8739'_204 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_step'45''8801''45''8739'_204 v5
du_step'45''8801''45''8739'_204 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8801''45''8739'_204 v0 = coe v0
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning.Base.step-≡-⟨
d_step'45''8801''45''10216'_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''45''10216'_206 ~v0 ~v1 ~v2
  = du_step'45''8801''45''10216'_206
du_step'45''8801''45''10216'_206 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8801''45''10216'_206
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning.Base.step-≡-⟩
d_step'45''8801''45''10217'_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''45''10217'_208 ~v0 ~v1 ~v2
  = du_step'45''8801''45''10217'_208
du_step'45''8801''45''10217'_208 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8801''45''10217'_208
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning.Base.step-≡˘
d_step'45''8801''728'_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''728'_210 ~v0 ~v1 ~v2 = du_step'45''8801''728'_210
du_step'45''8801''728'_210 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8801''728'_210
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning.Base.stop
d_stop_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_stop_212 ~v0 ~v1 v2 = du_stop_212 v2
du_stop_212 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_stop_212 v0
  = let v1 = coe du_'8621''45'setoid_178 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning.Base.∼-go
d_'8764''45'go_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_'8764''45'go_214 ~v0 ~v1 v2 = du_'8764''45'go_214 v2
du_'8764''45'go_214 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_'8764''45'go_214 v0
  = let v1 = coe du_'8621''45'setoid_178 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning.Base.≡-go
d_'8801''45'go_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_'8801''45'go_216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
  = du_'8801''45'go_216 v7
du_'8801''45'go_216 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_'8801''45'go_216 v0 = coe v0
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning._.step-↭
d_step'45''8621'_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8621'_224 ~v0 ~v1 ~v2 = du_step'45''8621'_224
du_step'45''8621'_224 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8621'_224
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621'_420
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
         (coe
            (\ v0 v1 v2 ->
               coe
                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                 (coe v1))))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning._.step-↭-⟨
d_step'45''8621''45''10216'_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8621''45''10216'_226 ~v0 ~v1 v2
  = du_step'45''8621''45''10216'_226 v2
du_step'45''8621''45''10216'_226 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8621''45''10216'_226 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10216'_418
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
         (coe
            (\ v1 v2 v3 ->
               coe
                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                 (coe v2))))
      (coe du_'8621''45'sym_96 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning._.step-↭-⟩
d_step'45''8621''45''10217'_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8621''45''10217'_228 ~v0 ~v1 ~v2
  = du_step'45''8621''45''10217'_228
du_step'45''8621''45''10217'_228 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8621''45''10217'_228
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
         (coe
            (\ v0 v1 v2 ->
               coe
                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                 (coe v1))))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning._.step-↭˘
d_step'45''8621''728'_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8621''728'_230 ~v0 ~v1 v2
  = du_step'45''8621''728'_230 v2
du_step'45''8621''728'_230 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8621''728'_230 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''728'_422
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
         (coe
            (\ v1 v2 v3 ->
               coe
                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                 (coe v2))))
      (coe du_'8621''45'sym_96 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning._.step-≋
d_step'45''8779'_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8779'_234 ~v0 ~v1 ~v2 = du_step'45''8779'_234
du_step'45''8779'_234 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8779'_234
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8779'_382
      (coe
         (\ v0 v1 v2 ->
            coe
              MAlonzo.Code.Function.Base.du__'8728''8242'__216
              (coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                 (coe
                    (\ v3 v4 v5 ->
                       coe
                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                         (coe v4)))
                 (coe v0) (coe v1) (coe v2))
              (coe
                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42)))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning._.step-≋-⟨
d_step'45''8779''45''10216'_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8779''45''10216'_236 ~v0 ~v1 v2
  = du_step'45''8779''45''10216'_236 v2
du_step'45''8779''45''10216'_236 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8779''45''10216'_236 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8779''45''10216'_380
      (coe
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Function.Base.du__'8728''8242'__216
              (coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                 (coe
                    (\ v4 v5 v6 ->
                       coe
                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                         (coe v5)))
                 (coe v1) (coe v2) (coe v3))
              (coe
                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42)))
      (let v1
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning._.step-≋-⟩
d_step'45''8779''45''10217'_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8779''45''10217'_238 ~v0 ~v1 ~v2
  = du_step'45''8779''45''10217'_238
du_step'45''8779''45''10217'_238 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8779''45''10217'_238
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8779''45''10217'_378
      (coe
         (\ v0 v1 v2 ->
            coe
              MAlonzo.Code.Function.Base.du__'8728''8242'__216
              (coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                 (coe
                    (\ v3 v4 v5 ->
                       coe
                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                         (coe v4)))
                 (coe v0) (coe v1) (coe v2))
              (coe
                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42)))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning._.step-≋˘
d_step'45''8779''728'_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8779''728'_240 ~v0 ~v1 v2
  = du_step'45''8779''728'_240 v2
du_step'45''8779''728'_240 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8779''728'_240 v0
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8779''728'_384
      (coe
         (\ v1 v2 v3 ->
            coe
              MAlonzo.Code.Function.Base.du__'8728''8242'__216
              (coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                 (coe
                    (\ v4 v5 v6 ->
                       coe
                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                         (coe v5)))
                 (coe v1) (coe v2) (coe v3))
              (coe
                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42)))
      (let v1
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))))
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning.step-prep
d_step'45'prep_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45'prep_250 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_step'45'prep_250 v2 v3 v4 v5 v6 v7 v8
du_step'45'prep_250 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45'prep_250 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
      (coe
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
              (coe v8)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v3))
      (coe v4)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
            v1)
         v6)
      (coe v5)
-- Data.List.Relation.Binary.Permutation.Setoid.PermutationReasoning.step-swap
d_step'45'swap_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45'swap_270 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8 v9
  = du_step'45'swap_270 v2 v3 v4 v5 v6 v7 v8 v9
du_step'45'swap_270 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45'swap_270 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
      (coe
         (\ v8 v9 v10 ->
            coe
              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
              (coe v9)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2) (coe v3)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v4)))
      (coe v5)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
            v1)
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
            v2)
         v7)
      (coe v6)
