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

module MAlonzo.Code.Data.Unit.Polymorphic.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Unit.Polymorphic.Properties._≟_
d__'8799'__10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Level.T_Lift_8 ->
  MAlonzo.Code.Level.T_Lift_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__10 ~v0 ~v1 ~v2 = du__'8799'__10
du__'8799'__10 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__10
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
-- Data.Unit.Polymorphic.Properties.≡-setoid
d_'8801''45'setoid_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'8801''45'setoid_14 ~v0 = du_'8801''45'setoid_14
du_'8801''45'setoid_14 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_'8801''45'setoid_14
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Unit.Polymorphic.Properties.≡-decSetoid
d_'8801''45'decSetoid_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_'8801''45'decSetoid_18 ~v0 = du_'8801''45'decSetoid_18
du_'8801''45'decSetoid_18 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
du_'8801''45'decSetoid_18
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
      (\ v0 v1 -> coe du__'8799'__10)
-- Data.Unit.Polymorphic.Properties.≡-total
d_'8801''45'total_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Level.T_Lift_8 ->
  MAlonzo.Code.Level.T_Lift_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8801''45'total_20 ~v0 ~v1 ~v2 = du_'8801''45'total_20
du_'8801''45'total_20 :: MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8801''45'total_20
  = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
-- Data.Unit.Polymorphic.Properties.≡-antisym
d_'8801''45'antisym_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Level.T_Lift_8 ->
  MAlonzo.Code.Level.T_Lift_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45'antisym_22 = erased
-- Data.Unit.Polymorphic.Properties.≡-isPreorder
d_'8801''45'isPreorder_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_'8801''45'isPreorder_28 ~v0 = du_'8801''45'isPreorder_28
du_'8801''45'isPreorder_28 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_'8801''45'isPreorder_28
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (coe (\ v0 v1 v2 -> v2)) erased
-- Data.Unit.Polymorphic.Properties.≡-isPartialOrder
d_'8801''45'isPartialOrder_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_'8801''45'isPartialOrder_36 ~v0 = du_'8801''45'isPartialOrder_36
du_'8801''45'isPartialOrder_36 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_'8801''45'isPartialOrder_36
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe du_'8801''45'isPreorder_28) erased
-- Data.Unit.Polymorphic.Properties.≡-isTotalOrder
d_'8801''45'isTotalOrder_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_'8801''45'isTotalOrder_42 ~v0 = du_'8801''45'isTotalOrder_42
du_'8801''45'isTotalOrder_42 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
du_'8801''45'isTotalOrder_42
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_540
      (coe du_'8801''45'isPartialOrder_36)
      (\ v0 v1 -> coe du_'8801''45'total_20)
-- Data.Unit.Polymorphic.Properties.≡-isDecTotalOrder
d_'8801''45'isDecTotalOrder_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_'8801''45'isDecTotalOrder_48 ~v0
  = du_'8801''45'isDecTotalOrder_48
du_'8801''45'isDecTotalOrder_48 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
du_'8801''45'isDecTotalOrder_48
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_618
      (coe du_'8801''45'isTotalOrder_42) (\ v0 v1 -> coe du__'8799'__10)
      (\ v0 v1 -> coe du__'8799'__10)
-- Data.Unit.Polymorphic.Properties.≡-preorder
d_'8801''45'preorder_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_'8801''45'preorder_54 ~v0 = du_'8801''45'preorder_54
du_'8801''45'preorder_54 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_'8801''45'preorder_54
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_232
      (coe du_'8801''45'isPreorder_28)
-- Data.Unit.Polymorphic.Properties.≡-poset
d_'8801''45'poset_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_'8801''45'poset_60 ~v0 = du_'8801''45'poset_60
du_'8801''45'poset_60 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_'8801''45'poset_60
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      (coe du_'8801''45'isPartialOrder_36)
-- Data.Unit.Polymorphic.Properties.≡-totalOrder
d_'8801''45'totalOrder_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
d_'8801''45'totalOrder_66 ~v0 = du_'8801''45'totalOrder_66
du_'8801''45'totalOrder_66 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
du_'8801''45'totalOrder_66
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1090
      (coe du_'8801''45'isTotalOrder_42)
-- Data.Unit.Polymorphic.Properties.≡-decTotalOrder
d_'8801''45'decTotalOrder_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
d_'8801''45'decTotalOrder_72 ~v0 = du_'8801''45'decTotalOrder_72
du_'8801''45'decTotalOrder_72 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
du_'8801''45'decTotalOrder_72
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1272
      (coe du_'8801''45'isDecTotalOrder_48)
-- Data.Unit.Polymorphic.Properties.⊤↔⊤*
d_'8868''8596''8868''42'_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'8868''8596''8868''42'_76 ~v0 = du_'8868''8596''8868''42'_76
du_'8868''8596''8868''42'_76 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'8868''8596''8868''42'_76
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596'_2526
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Level.C_lift_20
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
