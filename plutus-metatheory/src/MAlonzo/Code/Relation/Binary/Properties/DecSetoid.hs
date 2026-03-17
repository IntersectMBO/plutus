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

module MAlonzo.Code.Relation.Binary.Properties.DecSetoid where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Relation.Binary.Properties.DecSetoid._._≉_
d__'8777'__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86 ->
  AgdaAny -> AgdaAny -> ()
d__'8777'__18 = erased
-- Relation.Binary.Properties.DecSetoid.≉-cotrans
d_'8777''45'cotrans_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8777''45'cotrans_58 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_'8777''45'cotrans_58 v2 v3 v4 v5 v6
du_'8777''45'cotrans_58 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8777''45'cotrans_58 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Relation.Binary.Structures.d__'8799'__52
              (MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_102
                 (coe v0))
              v1 v4 in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Relation.Binary.Structures.d__'8799'__52
                 (MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_102
                    (coe v0))
                 v4 v2 in
       coe
         (let v7
                = case coe v5 of
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                      -> coe
                           seq (coe v7)
                           (coe
                              seq (coe v8)
                              (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError in
          coe
            (case coe v6 of
               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                 -> let v10
                          = case coe v5 of
                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                -> case coe v10 of
                                     MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                       -> case coe v11 of
                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                              -> coe
                                                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
                                            _ -> coe v7
                                     _ -> coe v7
                              _ -> MAlonzo.RTE.mazUnreachableError in
                    coe
                      (if coe v8
                         then case coe v5 of
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                  -> if coe v11
                                       then case coe v12 of
                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                                -> case coe v9 of
                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v14
                                                       -> coe
                                                            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                            (coe
                                                               (\ v15 ->
                                                                  coe
                                                                    v3
                                                                    (let v16
                                                                           = coe
                                                                               MAlonzo.Code.Relation.Binary.Bundles.du_setoid_110
                                                                               (coe v0) in
                                                                     coe
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                          (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                             (coe v16))
                                                                          v1 v4 v2 v13 v14))))
                                                     _ -> coe v10
                                              _ -> coe v10
                                       else (case coe v12 of
                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                 -> coe
                                                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                      erased
                                               _ -> coe v10)
                                _ -> MAlonzo.RTE.mazUnreachableError
                         else (let v11
                                     = case coe v5 of
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                           -> case coe v11 of
                                                MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                  -> case coe v12 of
                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                         -> coe
                                                              MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                                              erased
                                                       _ -> coe v10
                                                _ -> coe v10
                                         _ -> MAlonzo.RTE.mazUnreachableError in
                               coe
                                 (case coe v9 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                      -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
                                    _ -> coe v11)))
               _ -> MAlonzo.RTE.mazUnreachableError)))
-- Relation.Binary.Properties.DecSetoid.≉-isApartnessRelation
d_'8777''45'isApartnessRelation_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722
d_'8777''45'isApartnessRelation_106 ~v0 ~v1 v2
  = du_'8777''45'isApartnessRelation_106 v2
du_'8777''45'isApartnessRelation_106 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722
du_'8777''45'isApartnessRelation_106 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsApartnessRelation'46'constructor_32525
      erased (coe du_'8777''45'cotrans_58 (coe v0))
-- Relation.Binary.Properties.DecSetoid.≉-apartnessRelation
d_'8777''45'apartnessRelation_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_ApartnessRelation_1484
d_'8777''45'apartnessRelation_108 ~v0 ~v1 v2
  = du_'8777''45'apartnessRelation_108 v2
du_'8777''45'apartnessRelation_108 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_ApartnessRelation_1484
du_'8777''45'apartnessRelation_108 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_ApartnessRelation'46'constructor_28831
      (coe du_'8777''45'isApartnessRelation_106 (coe v0))
-- Relation.Binary.Properties.DecSetoid.≉-tight
d_'8777''45'tight_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8777''45'tight_110 ~v0 ~v1 v2 v3 v4
  = du_'8777''45'tight_110 v2 v3 v4
du_'8777''45'tight_110 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8777''45'tight_110 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v3 ->
         coe
           MAlonzo.Code.Relation.Nullary.Decidable.Core.du_decidable'45'stable_198
           (coe
              MAlonzo.Code.Relation.Binary.Structures.d__'8799'__52
              (MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_102
                 (coe v0))
              v1 v2))
      erased
