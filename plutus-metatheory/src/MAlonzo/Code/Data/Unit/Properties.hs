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

module MAlonzo.Code.Data.Unit.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.Unit.Properties.⊤-irrelevant
d_'8868''45'irrelevant_6 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8868''45'irrelevant_6 = erased
-- Data.Unit.Properties._≟_
d__'8799'__8 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__8 ~v0 ~v1 = du__'8799'__8
du__'8799'__8 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8799'__8
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
-- Data.Unit.Properties.≡-setoid
d_'8801''45'setoid_10 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'8801''45'setoid_10
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Unit.Properties.≡-decSetoid
d_'8801''45'decSetoid_12 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_'8801''45'decSetoid_12
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
      (\ v0 v1 -> coe du__'8799'__8)
-- Data.Unit.Properties.≡-total
d_'8801''45'total_14 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8801''45'total_14 ~v0 ~v1 = du_'8801''45'total_14
du_'8801''45'total_14 :: MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8801''45'total_14
  = coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
-- Data.Unit.Properties.≡-antisym
d_'8801''45'antisym_16 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45'antisym_16 = erased
-- Data.Unit.Properties.≡-isPreorder
d_'8801''45'isPreorder_20 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_'8801''45'isPreorder_20
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (coe (\ v0 v1 v2 -> v2)) erased
-- Data.Unit.Properties.≡-isPartialOrder
d_'8801''45'isPartialOrder_24 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_'8801''45'isPartialOrder_24
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe d_'8801''45'isPreorder_20) erased
-- Data.Unit.Properties.≡-isTotalOrder
d_'8801''45'isTotalOrder_26 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_'8801''45'isTotalOrder_26
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_540
      (coe d_'8801''45'isPartialOrder_24)
      (\ v0 v1 -> coe du_'8801''45'total_14)
-- Data.Unit.Properties.≡-isDecTotalOrder
d_'8801''45'isDecTotalOrder_28 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_'8801''45'isDecTotalOrder_28
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_618
      (coe d_'8801''45'isTotalOrder_26) (\ v0 v1 -> coe du__'8799'__8)
      (\ v0 v1 -> coe du__'8799'__8)
-- Data.Unit.Properties.≡-poset
d_'8801''45'poset_30 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_'8801''45'poset_30
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      d_'8801''45'isPartialOrder_24
-- Data.Unit.Properties.≡-decTotalOrder
d_'8801''45'decTotalOrder_32 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
d_'8801''45'decTotalOrder_32
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1272
      d_'8801''45'isDecTotalOrder_28
