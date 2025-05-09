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

module MAlonzo.Code.Data.Unit.Polymorphic.Properties where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Level qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8801''45'setoid_14 ~v0 = du_'8801''45'setoid_14
du_'8801''45'setoid_14 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_'8801''45'setoid_14
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Unit.Polymorphic.Properties.≡-decSetoid
d_'8801''45'decSetoid_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_'8801''45'decSetoid_18 ~v0 = du_'8801''45'decSetoid_18
du_'8801''45'decSetoid_18 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
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
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8801''45'isPreorder_28 ~v0 = du_'8801''45'isPreorder_28
du_'8801''45'isPreorder_28 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_'8801''45'isPreorder_28
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (coe (\ v0 v1 v2 -> v2)) erased
-- Data.Unit.Polymorphic.Properties.≡-isPartialOrder
d_'8801''45'isPartialOrder_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_'8801''45'isPartialOrder_36 ~v0 = du_'8801''45'isPartialOrder_36
du_'8801''45'isPartialOrder_36 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_'8801''45'isPartialOrder_36
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_9853
      (coe du_'8801''45'isPreorder_28) erased
-- Data.Unit.Polymorphic.Properties.≡-isTotalOrder
d_'8801''45'isTotalOrder_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
d_'8801''45'isTotalOrder_42 ~v0 = du_'8801''45'isTotalOrder_42
du_'8801''45'isTotalOrder_42 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
du_'8801''45'isTotalOrder_42
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalOrder'46'constructor_20555
      (coe du_'8801''45'isPartialOrder_36)
      (\ v0 v1 -> coe du_'8801''45'total_20)
-- Data.Unit.Polymorphic.Properties.≡-isDecTotalOrder
d_'8801''45'isDecTotalOrder_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
d_'8801''45'isDecTotalOrder_48 ~v0
  = du_'8801''45'isDecTotalOrder_48
du_'8801''45'isDecTotalOrder_48 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
du_'8801''45'isDecTotalOrder_48
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecTotalOrder'46'constructor_22695
      (coe du_'8801''45'isTotalOrder_42) (\ v0 v1 -> coe du__'8799'__10)
      (\ v0 v1 -> coe du__'8799'__10)
-- Data.Unit.Polymorphic.Properties.≡-preorder
d_'8801''45'preorder_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_'8801''45'preorder_54 ~v0 = du_'8801''45'preorder_54
du_'8801''45'preorder_54 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_'8801''45'preorder_54
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2267
      (coe du_'8801''45'isPreorder_28)
-- Data.Unit.Polymorphic.Properties.≡-poset
d_'8801''45'poset_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_'8801''45'poset_60 ~v0 = du_'8801''45'poset_60
du_'8801''45'poset_60 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_'8801''45'poset_60
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_6389
      (coe du_'8801''45'isPartialOrder_36)
-- Data.Unit.Polymorphic.Properties.≡-totalOrder
d_'8801''45'totalOrder_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
d_'8801''45'totalOrder_66 ~v0 = du_'8801''45'totalOrder_66
du_'8801''45'totalOrder_66 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
du_'8801''45'totalOrder_66
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalOrder'46'constructor_15747
      (coe du_'8801''45'isTotalOrder_42)
-- Data.Unit.Polymorphic.Properties.≡-decTotalOrder
d_'8801''45'decTotalOrder_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
d_'8801''45'decTotalOrder_72 ~v0 = du_'8801''45'decTotalOrder_72
du_'8801''45'decTotalOrder_72 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
du_'8801''45'decTotalOrder_72
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecTotalOrder'46'constructor_17849
      (coe du_'8801''45'isDecTotalOrder_48)
-- Data.Unit.Polymorphic.Properties.⊤↔⊤*
d_'8868''8596''8868''42'_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8868''8596''8868''42'_76 ~v0 = du_'8868''8596''8868''42'_76
du_'8868''8596''8868''42'_76 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8868''8596''8868''42'_76
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596'_2350
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Level.C_lift_20
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
