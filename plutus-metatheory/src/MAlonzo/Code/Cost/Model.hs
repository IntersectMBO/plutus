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

module MAlonzo.Code.Cost.Model where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Constant.AtomicType
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Cost.Raw
import qualified MAlonzo.Code.Cost.Size
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Char.Properties
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.NonEmpty.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Untyped.CEK
import qualified MAlonzo.Code.Utils

-- Cost.Model.Intercept
d_Intercept_4 :: ()
d_Intercept_4 = erased
-- Cost.Model.Slope
d_Slope_6 :: ()
d_Slope_6 = erased
-- Cost.Model.CostingModel
d_CostingModel_8 a0 = ()
data T_CostingModel_8
  = C_constantCost_12 Integer |
    C_linearCostIn_16 MAlonzo.Code.Data.Fin.Base.T_Fin_10 Integer
                      Integer |
    C_quadraticCostIn1_20 MAlonzo.Code.Data.Fin.Base.T_Fin_10 Integer
                          Integer Integer |
    C_quadraticCostIn2_24 MAlonzo.Code.Data.Fin.Base.T_Fin_10
                          MAlonzo.Code.Data.Fin.Base.T_Fin_10 Integer Integer Integer Integer
                          Integer Integer Integer |
    C_literalCostIn_28 MAlonzo.Code.Data.Fin.Base.T_Fin_10
                       T_CostingModel_8 |
    C_addedSizes_32 Integer Integer |
    C_multipliedSizes_36 Integer Integer |
    C_minSize_40 Integer Integer | C_maxSize_44 Integer Integer |
    C_twoArgumentsSubtractedSizes_46 Integer Integer Integer |
    C_twoArgumentsConstAboveDiagonal_48 Integer T_CostingModel_8 |
    C_twoArgumentsConstBelowDiagonal_50 Integer T_CostingModel_8 |
    C_twoArgumentsConstOffDiagonal_52 Integer T_CostingModel_8 |
    C_twoArgumentsLinearInYAndZ_54 Integer Integer Integer |
    C_twoArgumentsLinearInMaxYZ_56 Integer Integer |
    C_threeArgumentsExpModCost_58 Integer Integer Integer
-- Cost.Model.BuiltinModel
d_BuiltinModel_62 a0 = ()
data T_BuiltinModel_62
  = C_BuiltinModel'46'constructor_607 T_CostingModel_8
                                      T_CostingModel_8
-- Cost.Model.BuiltinModel.costingCPU
d_costingCPU_70 :: T_BuiltinModel_62 -> T_CostingModel_8
d_costingCPU_70 v0
  = case coe v0 of
      C_BuiltinModel'46'constructor_607 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Model.BuiltinModel.costingMem
d_costingMem_72 :: T_BuiltinModel_62 -> T_CostingModel_8
d_costingMem_72 v0
  = case coe v0 of
      C_BuiltinModel'46'constructor_607 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Model.prod
d_prod_76 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_prod_76 v0
  = coe
      MAlonzo.Code.Data.Vec.Base.du_foldr_352 (coe v0)
      (coe (\ v1 -> mulInt)) (coe (1 :: Integer))
-- Cost.Model.maximum
d_maximum_80 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_maximum_80 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> coe
             MAlonzo.Code.Data.Vec.Base.du_foldr_352 (coe v0)
             (coe (\ v5 -> MAlonzo.Code.Data.Nat.Base.d__'8852'__204)) (coe v3)
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Model.minimum
d_minimum_84 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_minimum_84 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3 v4
        -> coe
             MAlonzo.Code.Data.Vec.Base.du_foldr_352 (coe v0)
             (coe (\ v5 -> MAlonzo.Code.Data.Nat.Base.d__'8851'__232)) (coe v3)
             (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Model.runModel
d_runModel_96 ::
  Integer ->
  T_CostingModel_8 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_runModel_96 v0 v1 v2
  = case coe v1 of
      C_constantCost_12 v4 -> coe v4
      C_linearCostIn_16 v4 v5 v6
        -> coe
             addInt
             (coe
                mulInt (coe v6)
                (coe
                   MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                   (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v2) (coe v4))))
             (coe v5)
      C_quadraticCostIn1_20 v4 v5 v6 v7
        -> coe
             addInt
             (coe
                addInt
                (coe
                   mulInt
                   (coe
                      mulInt (coe v7)
                      (coe
                         MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                         (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v2) (coe v4))))
                   (coe
                      MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                      (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v2) (coe v4))))
                (coe
                   mulInt (coe v6)
                   (coe
                      MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                      (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v2) (coe v4)))))
             (coe v5)
      C_quadraticCostIn2_24 v4 v5 v6 v7 v8 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v6)
             (coe
                addInt
                (coe
                   addInt
                   (coe
                      addInt
                      (coe
                         addInt
                         (coe
                            addInt
                            (coe
                               mulInt
                               (coe
                                  mulInt (coe v10)
                                  (coe
                                     MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                     (coe
                                        MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v2) (coe v4))))
                               (coe
                                  MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                  (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v2) (coe v4))))
                            (coe
                               mulInt
                               (coe
                                  mulInt (coe v11)
                                  (coe
                                     MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                     (coe
                                        MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v2) (coe v4))))
                               (coe
                                  MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                  (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v2) (coe v5)))))
                         (coe
                            mulInt
                            (coe
                               mulInt (coe v12)
                               (coe
                                  MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                  (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v2) (coe v5))))
                            (coe
                               MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                               (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v2) (coe v5)))))
                      (coe
                         mulInt (coe v8)
                         (coe
                            MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                            (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v2) (coe v4)))))
                   (coe
                      mulInt (coe v9)
                      (coe
                         MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                         (coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v2) (coe v5)))))
                (coe v7))
      C_literalCostIn_28 v4 v5
        -> let v6
                 = coe MAlonzo.Code.Data.Vec.Base.du_lookup_82 (coe v2) (coe v4) in
           coe
             (let v7 = d_runModel_96 (coe v0) (coe v5) (coe v2) in
              coe
                (case coe v6 of
                   MAlonzo.Code.Untyped.CEK.C_V'45'con_50 v8 v9
                     -> case coe v8 of
                          MAlonzo.Code.Builtin.Signature.C_atomic_12 v11
                            -> case coe v11 of
                                 MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                                   -> case coe v9 of
                                        _ | coe geqInt (coe v9) (coe (1 :: Integer)) ->
                                            let v12 = subInt (coe v9) (coe (1 :: Integer)) in
                                            coe
                                              (coe
                                                 addInt (coe (1 :: Integer))
                                                 (coe
                                                    MAlonzo.Code.Data.Nat.Base.du__'47'__314
                                                    (coe v12) (coe (8 :: Integer))))
                                        0 -> coe v7
                                        _ -> coe v7
                                 _ -> coe v7
                          _ -> coe v7
                   _ -> coe v7))
      C_addedSizes_32 v4 v5
        -> coe
             addInt
             (coe
                mulInt (coe v5)
                (coe
                   MAlonzo.Code.Data.Vec.Base.d_sum_420 v0
                   (coe
                      MAlonzo.Code.Data.Vec.Base.du_map_178
                      (coe MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78) (coe v2))))
             (coe v4)
      C_multipliedSizes_36 v4 v5
        -> coe
             addInt
             (coe
                mulInt (coe v5)
                (coe
                   d_prod_76 v0
                   (coe
                      MAlonzo.Code.Data.Vec.Base.du_map_178
                      (coe MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78) (coe v2))))
             (coe v4)
      C_minSize_40 v4 v5
        -> let v6 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                addInt
                (coe
                   mulInt (coe v5)
                   (coe
                      d_minimum_84 (coe v6)
                      (coe
                         MAlonzo.Code.Data.Vec.Base.du_map_178
                         (coe MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78) (coe v2))))
                (coe v4))
      C_maxSize_44 v4 v5
        -> let v6 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                addInt
                (coe
                   mulInt (coe v5)
                   (coe
                      d_maximum_80 (coe v6)
                      (coe
                         MAlonzo.Code.Data.Vec.Base.du_map_178
                         (coe MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78) (coe v2))))
                (coe v4))
      C_twoArgumentsSubtractedSizes_46 v3 v4 v5
        -> case coe v2 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v10 v11
                      -> coe
                           addInt
                           (coe
                              mulInt (coe v4)
                              (coe
                                 MAlonzo.Code.Data.Nat.Base.d__'8852'__204 (coe v5)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22
                                    (MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78 (coe v7))
                                    (MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78 (coe v10)))))
                           (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_twoArgumentsConstAboveDiagonal_48 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                      -> coe
                           seq (coe v10)
                           (coe
                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                              (coe
                                 ltInt
                                 (coe MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78 (coe v6))
                                 (coe MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78 (coe v9)))
                              (coe v3)
                              (coe
                                 d_runModel_96 (coe (2 :: Integer)) (coe v4)
                                 (coe
                                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6
                                    (coe
                                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9
                                       (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_twoArgumentsConstBelowDiagonal_50 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                      -> coe
                           seq (coe v10)
                           (coe
                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                              (coe
                                 ltInt
                                 (coe MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78 (coe v9))
                                 (coe MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78 (coe v6)))
                              (coe v3)
                              (coe
                                 d_runModel_96 (coe (2 :: Integer)) (coe v4)
                                 (coe
                                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6
                                    (coe
                                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9
                                       (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_twoArgumentsConstOffDiagonal_52 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                      -> coe
                           seq (coe v10)
                           (coe
                              MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                              (coe
                                 MAlonzo.Code.Data.Bool.Base.d_not_22
                                 (coe
                                    eqInt
                                    (coe MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78 (coe v6))
                                    (coe MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78 (coe v9))))
                              (coe v3)
                              (coe
                                 d_runModel_96 (coe (2 :: Integer)) (coe v4)
                                 (coe
                                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6
                                    (coe
                                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9
                                       (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_twoArgumentsLinearInYAndZ_54 v3 v4 v5
        -> case coe v2 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v10 v11
                      -> case coe v11 of
                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v13 v14
                             -> coe
                                  addInt
                                  (coe
                                     addInt
                                     (coe
                                        mulInt (coe v4)
                                        (coe
                                           MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                           (coe v10)))
                                     (coe
                                        mulInt (coe v5)
                                        (coe
                                           MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                           (coe v13))))
                                  (coe v3)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_twoArgumentsLinearInMaxYZ_56 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6 v7
               -> case coe v7 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v9 v10
                      -> case coe v10 of
                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v12 v13
                             -> coe
                                  addInt
                                  (coe
                                     mulInt (coe v4)
                                     (coe
                                        d_maximum_80 (coe (1 :: Integer))
                                        (coe
                                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                           (MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                              (coe v9))
                                           (coe
                                              MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                                              (MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                 (coe v12))
                                              (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32)))))
                                  (coe v3)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_threeArgumentsExpModCost_58 v3 v4 v5
        -> case coe v2 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8
               -> case coe v8 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v10 v11
                      -> case coe v11 of
                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v13 v14
                             -> coe
                                  seq (coe v14)
                                  (coe
                                     MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                                     (coe
                                        ltInt
                                        (coe
                                           MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                           (coe v13))
                                        (coe
                                           MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                           (coe v7)))
                                     (coe
                                        addInt
                                        (coe
                                           addInt
                                           (coe
                                              addInt
                                              (coe
                                                 MAlonzo.Code.Data.Nat.Base.du__'47'__314
                                                 (coe
                                                    addInt
                                                    (coe
                                                       addInt
                                                       (coe
                                                          mulInt
                                                          (coe
                                                             mulInt
                                                             (coe
                                                                mulInt (coe v5)
                                                                (coe
                                                                   MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                                   (coe v10)))
                                                             (coe
                                                                MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                                (coe v13)))
                                                          (coe
                                                             MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                             (coe v13)))
                                                       (coe
                                                          mulInt
                                                          (coe
                                                             mulInt (coe v4)
                                                             (coe
                                                                MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                                (coe v10)))
                                                          (coe
                                                             MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                             (coe v13))))
                                                    (coe v3))
                                                 (coe (2 :: Integer)))
                                              (coe
                                                 mulInt
                                                 (coe
                                                    mulInt
                                                    (coe
                                                       mulInt (coe v5)
                                                       (coe
                                                          MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                          (coe v10)))
                                                    (coe
                                                       MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                       (coe v13)))
                                                 (coe
                                                    MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                    (coe v13))))
                                           (coe
                                              mulInt
                                              (coe
                                                 mulInt (coe v4)
                                                 (coe
                                                    MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                    (coe v10)))
                                              (coe
                                                 MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                 (coe v13))))
                                        (coe v3))
                                     (coe
                                        addInt
                                        (coe
                                           addInt
                                           (coe
                                              mulInt
                                              (coe
                                                 mulInt
                                                 (coe
                                                    mulInt (coe v5)
                                                    (coe
                                                       MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                       (coe v10)))
                                                 (coe
                                                    MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                    (coe v13)))
                                              (coe
                                                 MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                 (coe v13)))
                                           (coe
                                              mulInt
                                              (coe
                                                 mulInt (coe v4)
                                                 (coe
                                                    MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                    (coe v10)))
                                              (coe
                                                 MAlonzo.Code.Cost.Size.d_defaultValueMeasure_78
                                                 (coe v13))))
                                        (coe v3)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Model.convertRawModel
d_convertRawModel_292 ::
  Integer ->
  MAlonzo.Code.Cost.Raw.T_RawModel_144 -> Maybe T_CostingModel_8
d_convertRawModel_292 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Cost.Raw.C_ConstantCost_146 v3
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe C_constantCost_12 v3)
         MAlonzo.Code.Cost.Raw.C_AddedSizes_148 v3
           -> case coe v3 of
                MAlonzo.Code.Cost.Raw.C_mkLinearFunction_42 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_addedSizes_32 v4 v5)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Cost.Raw.C_MultipliedSizes_150 v3
           -> case coe v3 of
                MAlonzo.Code.Cost.Raw.C_mkLinearFunction_42 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe C_multipliedSizes_36 v4 v5)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Cost.Raw.C_MinSize_152 v3
           -> case coe v0 of
                _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
                    case coe v3 of
                      MAlonzo.Code.Cost.Raw.C_mkLinearFunction_42 v4 v5
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_minSize_40 v4 v5)
                      _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_MaxSize_154 v3
           -> case coe v0 of
                _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
                    case coe v3 of
                      MAlonzo.Code.Cost.Raw.C_mkLinearFunction_42 v4 v5
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_maxSize_44 v4 v5)
                      _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_LinearInX_156 v3
           -> case coe v0 of
                _ | coe geqInt (coe v0) (coe (1 :: Integer)) ->
                    case coe v3 of
                      MAlonzo.Code.Cost.Raw.C_mkLinearFunction_42 v4 v5
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                C_linearCostIn_16 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) v4 v5)
                      _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_LinearInY_158 v3
           -> case coe v0 of
                _ | coe geqInt (coe v0) (coe (2 :: Integer)) ->
                    case coe v3 of
                      MAlonzo.Code.Cost.Raw.C_mkLinearFunction_42 v4 v5
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                C_linearCostIn_16
                                (coe
                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                   (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                v4 v5)
                      _ -> MAlonzo.RTE.mazUnreachableError
                1 -> coe v2
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_LinearInZ_160 v3
           -> case coe v0 of
                _ | coe geqInt (coe v0) (coe (3 :: Integer)) ->
                    case coe v3 of
                      MAlonzo.Code.Cost.Raw.C_mkLinearFunction_42 v4 v5
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                C_linearCostIn_16
                                (coe
                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                   (coe
                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                v4 v5)
                      _ -> MAlonzo.RTE.mazUnreachableError
                2 -> coe v2
                1 -> coe v2
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_LiteralInYOrLinearInZ_164 v3
           -> case coe v0 of
                _ | coe geqInt (coe v0) (coe (3 :: Integer)) ->
                    case coe v3 of
                      MAlonzo.Code.Cost.Raw.C_mkLinearFunction_42 v4 v5
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                C_literalCostIn_28
                                (coe
                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                   (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                (coe
                                   C_linearCostIn_16
                                   (coe
                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                      (coe
                                         MAlonzo.Code.Data.Fin.Base.C_suc_16
                                         (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                   v4 v5))
                      _ -> MAlonzo.RTE.mazUnreachableError
                2 -> coe v2
                1 -> coe v2
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_LinearInMaxYZ_166 v3
           -> case coe v0 of
                3 -> case coe v3 of
                       MAlonzo.Code.Cost.Raw.C_mkLinearFunction_42 v4 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe C_twoArgumentsLinearInMaxYZ_56 (coe v4) (coe v5))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ | coe geqInt (coe v0) (coe (3 :: Integer)) -> coe v2
                2 -> coe v2
                1 -> coe v2
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_LinearInYAndZ_170 v3
           -> case coe v0 of
                3 -> case coe v3 of
                       MAlonzo.Code.Cost.Raw.C_mkTwoVariableLinearFunction_74 v4 v5 v6
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe C_twoArgumentsLinearInYAndZ_54 (coe v4) (coe v5) (coe v6))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ | coe geqInt (coe v0) (coe (3 :: Integer)) -> coe v2
                2 -> coe v2
                1 -> coe v2
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_QuadraticInX_172 v3
           -> case coe v0 of
                _ | coe geqInt (coe v0) (coe (2 :: Integer)) ->
                    case coe v3 of
                      MAlonzo.Code.Cost.Raw.C_mkOneVariableQuadraticFunction_58 v4 v5 v6
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                C_quadraticCostIn1_20 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) v4
                                v5 v6)
                      _ -> MAlonzo.RTE.mazUnreachableError
                1 -> coe v2
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_QuadraticInY_174 v3
           -> case coe v0 of
                _ | coe geqInt (coe v0) (coe (2 :: Integer)) ->
                    case coe v3 of
                      MAlonzo.Code.Cost.Raw.C_mkOneVariableQuadraticFunction_58 v4 v5 v6
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                C_quadraticCostIn1_20
                                (coe
                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                   (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                v4 v5 v6)
                      _ -> MAlonzo.RTE.mazUnreachableError
                1 -> coe v2
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_QuadraticInZ_176 v3
           -> case coe v0 of
                _ | coe geqInt (coe v0) (coe (3 :: Integer)) ->
                    case coe v3 of
                      MAlonzo.Code.Cost.Raw.C_mkOneVariableQuadraticFunction_58 v4 v5 v6
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                C_quadraticCostIn1_20
                                (coe
                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                   (coe
                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                      (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
                                v4 v5 v6)
                      _ -> MAlonzo.RTE.mazUnreachableError
                2 -> coe v2
                1 -> coe v2
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_QuadraticInXAndY_178 v3
           -> case coe v0 of
                _ | coe geqInt (coe v0) (coe (2 :: Integer)) ->
                    case coe v3 of
                      MAlonzo.Code.Cost.Raw.C_mkTwoVariableQuadraticFunction_106 v4 v5 v6 v7 v8 v9 v10
                        -> coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe
                                C_quadraticCostIn2_24 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                (coe
                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                   (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                v4 v5 v6 v7 v8 v9 v10)
                      _ -> MAlonzo.RTE.mazUnreachableError
                1 -> coe v2
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_SubtractedSizes_182 v3 v4
           -> case coe v0 of
                2 -> case coe v3 of
                       MAlonzo.Code.Cost.Raw.C_mkLinearFunction_42 v5 v6
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe C_twoArgumentsSubtractedSizes_46 (coe v5) (coe v6) (coe v4))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ | coe geqInt (coe v0) (coe (2 :: Integer)) -> coe v2
                1 -> coe v2
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_ConstAboveDiagonal_184 v3 v4
           -> case coe v0 of
                2 -> coe
                       MAlonzo.Code.Data.Maybe.Base.du_map_64
                       (coe C_twoArgumentsConstAboveDiagonal_48 (coe v3))
                       (d_convertRawModel_292 (coe (2 :: Integer)) (coe v4))
                _ | coe geqInt (coe v0) (coe (2 :: Integer)) -> coe v2
                1 -> coe v2
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_ConstBelowDiagonal_186 v3 v4
           -> case coe v0 of
                2 -> coe
                       MAlonzo.Code.Data.Maybe.Base.du_map_64
                       (coe C_twoArgumentsConstBelowDiagonal_50 (coe v3))
                       (d_convertRawModel_292 (coe (2 :: Integer)) (coe v4))
                _ | coe geqInt (coe v0) (coe (2 :: Integer)) -> coe v2
                1 -> coe v2
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_ConstOffDiagonal_188 v3 v4
           -> case coe v0 of
                2 -> coe
                       MAlonzo.Code.Data.Maybe.Base.du_map_64
                       (coe C_twoArgumentsConstOffDiagonal_52 (coe v3))
                       (d_convertRawModel_292 (coe (2 :: Integer)) (coe v4))
                _ | coe geqInt (coe v0) (coe (2 :: Integer)) -> coe v2
                1 -> coe v2
                _ -> coe v2
         MAlonzo.Code.Cost.Raw.C_ExpModCost_190 v3
           -> case coe v0 of
                3 -> case coe v3 of
                       MAlonzo.Code.Cost.Raw.C_mkExpModCostingFunction_142 v4 v5 v6
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe C_threeArgumentsExpModCost_58 (coe v4) (coe v5) (coe v6))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ | coe geqInt (coe v0) (coe (3 :: Integer)) -> coe v2
                2 -> coe v2
                1 -> coe v2
                _ -> coe v2
         _ -> coe v2)
-- Cost.Model.convertCpuAndMemoryModel
d_convertCpuAndMemoryModel_416 ::
  Integer ->
  MAlonzo.Code.Cost.Raw.T_CpuAndMemoryModel_192 ->
  Maybe T_BuiltinModel_62
d_convertCpuAndMemoryModel_416 v0 v1
  = case coe v1 of
      MAlonzo.Code.Cost.Raw.C_mkCpuAndMemoryModel_202 v2 v3
        -> let v4 = d_convertRawModel_292 (coe v0) (coe v2) in
           coe
             (let v5 = d_convertRawModel_292 (coe v0) (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                 (coe C_BuiltinModel'46'constructor_607 (coe v6) (coe v7))
                          _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Model.getModel
d_getModel_440 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Utils.T_List_384
    (MAlonzo.Code.Utils.T__'215'__366
       MAlonzo.Code.Agda.Builtin.String.T_String_6
       MAlonzo.Code.Cost.Raw.T_CpuAndMemoryModel_192) ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_getModel_440 v0 v1
  = case coe v1 of
      MAlonzo.Code.Utils.C_'91''93'_388
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Utils.C__'8759'__390 v2 v3
        -> case coe v2 of
             MAlonzo.Code.Utils.C__'44'__380 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_122
                            (coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe MAlonzo.Code.Builtin.d_showBuiltin_428 (coe v0)))
                               (coe
                                  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
                                  (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
                                     (MAlonzo.Code.Builtin.d_showBuiltin_428 (coe v0)))
                                  (coe
                                     MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v4))) in
                  coe
                    (if coe v6
                       then coe
                              MAlonzo.Code.Data.Maybe.Base.du_map_64
                              (\ v7 ->
                                 coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v7))
                              (d_convertCpuAndMemoryModel_416
                                 (coe
                                    addInt (coe (1 :: Integer))
                                    (coe
                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                       (coe (\ v7 v8 -> addInt (coe (1 :: Integer)) (coe v8)))
                                       (coe (0 :: Integer))
                                       (coe
                                          MAlonzo.Code.Data.List.NonEmpty.Base.d_tail_32
                                          (coe
                                             MAlonzo.Code.Builtin.Signature.d_args_86
                                             (coe MAlonzo.Code.Builtin.d_signature_298 (coe v0))))))
                                 (coe v5))
                       else coe d_getModel_440 (coe v0) (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Model.dummyModel
d_dummyModel_476 :: Integer -> T_BuiltinModel_62
d_dummyModel_476 ~v0 = du_dummyModel_476
du_dummyModel_476 :: T_BuiltinModel_62
du_dummyModel_476
  = coe
      C_BuiltinModel'46'constructor_607
      (coe C_constantCost_12 (0 :: Integer))
      (coe C_constantCost_12 (0 :: Integer))
-- Cost.Model.lookupModel
d_lookupModel_482 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Builtin.T_Builtin_2 -> T_BuiltinModel_62
d_lookupModel_482 v0 v1
  = case coe v0 of
      [] -> coe du_dummyModel_476
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = MAlonzo.Code.Builtin.d_decBuiltin_426 (coe v4) (coe v1) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe seq (coe v8) (coe v5)
                              else coe d_lookupModel_482 (coe v3) (coe v1)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Model.allJust
d_allJust_518 :: () -> [Maybe AgdaAny] -> Maybe [AgdaAny]
d_allJust_518 ~v0 v1 = du_allJust_518 v1
du_allJust_518 :: [Maybe AgdaAny] -> Maybe [AgdaAny]
du_allJust_518 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v0)
      (:) v1 v2
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> let v4 = coe du_allJust_518 (coe v2) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v5))
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v4
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Cost.Model.ModelAssignment
d_ModelAssignment_540 :: ()
d_ModelAssignment_540 = erased
-- Cost.Model.createMap
d_createMap_544 ::
  MAlonzo.Code.Utils.T_List_384
    (MAlonzo.Code.Utils.T__'215'__366
       MAlonzo.Code.Agda.Builtin.String.T_String_6
       MAlonzo.Code.Cost.Raw.T_CpuAndMemoryModel_192) ->
  Maybe (MAlonzo.Code.Builtin.T_Builtin_2 -> T_BuiltinModel_62)
d_createMap_544 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_map_64 d_lookupModel_482
      (coe
         du_allJust_518
         (coe
            MAlonzo.Code.Data.List.Base.du_map_22
            (coe (\ v1 -> d_getModel_440 (coe v1) (coe v0)))
            (coe MAlonzo.Code.Builtin.d_builtinList_430)))
