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

module MAlonzo.Code.Data.Word64.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.On
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.Word64.Properties.≈⇒≡
d_'8776''8658''8801'_6 ::
  MAlonzo.RTE.Word64 ->
  MAlonzo.RTE.Word64 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658''8801'_6 = erased
-- Data.Word64.Properties.≈-reflexive
d_'8776''45'reflexive_8 ::
  MAlonzo.RTE.Word64 ->
  MAlonzo.RTE.Word64 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''45'reflexive_8 = erased
-- Data.Word64.Properties.≈-refl
d_'8776''45'refl_10 ::
  MAlonzo.RTE.Word64 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''45'refl_10 = erased
-- Data.Word64.Properties.≈-sym
d_'8776''45'sym_12 ::
  MAlonzo.RTE.Word64 ->
  MAlonzo.RTE.Word64 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''45'sym_12 = erased
-- Data.Word64.Properties.≈-trans
d_'8776''45'trans_14 ::
  MAlonzo.RTE.Word64 ->
  MAlonzo.RTE.Word64 ->
  MAlonzo.RTE.Word64 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''45'trans_14 = erased
-- Data.Word64.Properties.≈-subst
d_'8776''45'subst_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.RTE.Word64 -> ()) ->
  MAlonzo.RTE.Word64 ->
  MAlonzo.RTE.Word64 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_'8776''45'subst_18 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8776''45'subst_18 v5
du_'8776''45'subst_18 :: AgdaAny -> AgdaAny
du_'8776''45'subst_18 v0 = coe v0
-- Data.Word64.Properties._≈?_
d__'8776''63'__26 ::
  MAlonzo.RTE.Word64 ->
  MAlonzo.RTE.Word64 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8776''63'__26 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796
      (coe word64ToNat (coe v0)) (coe word64ToNat (coe v1))
-- Data.Word64.Properties.≈-isEquivalence
d_'8776''45'isEquivalence_32 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_32
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_46 erased
      erased erased
-- Data.Word64.Properties.≈-setoid
d_'8776''45'setoid_46 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'8776''45'setoid_46
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      d_'8776''45'isEquivalence_32
-- Data.Word64.Properties.≈-isDecEquivalence
d_'8776''45'isDecEquivalence_48 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_'8776''45'isDecEquivalence_48
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_70
      (coe d_'8776''45'isEquivalence_32) (coe d__'8776''63'__26)
-- Data.Word64.Properties.≈-decSetoid
d_'8776''45'decSetoid_50 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_'8776''45'decSetoid_50
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_134
      d_'8776''45'isDecEquivalence_48
-- Data.Word64.Properties._≟_
d__'8799'__52 ::
  MAlonzo.RTE.Word64 ->
  MAlonzo.RTE.Word64 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__52 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      erased erased (coe d__'8776''63'__26 (coe v0) (coe v1))
-- Data.Word64.Properties.≡-setoid
d_'8801''45'setoid_58 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'8801''45'setoid_58
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Word64.Properties.≡-decSetoid
d_'8801''45'decSetoid_60 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_'8801''45'decSetoid_60
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
      (coe d__'8799'__52)
-- Data.Word64.Properties._==_
d__'61''61'__62 :: MAlonzo.RTE.Word64 -> MAlonzo.RTE.Word64 -> Bool
d__'61''61'__62 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_'8970'_'8971'_140 ()
      erased (d__'8799'__52 (coe v0) (coe v1))
-- Data.Word64.Properties._<?_
d__'60''63'__68 ::
  MAlonzo.RTE.Word64 ->
  MAlonzo.RTE.Word64 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__68
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_decidable_102
      (coe word64ToNat)
      (coe MAlonzo.Code.Data.Nat.Properties.d__'60''63'__3172)
-- Data.Word64.Properties.<-strictTotalOrder-≈
d_'60''45'strictTotalOrder'45''8776'_70 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
d_'60''45'strictTotalOrder'45''8776'_70
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_strictTotalOrder_650
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'60''45'strictTotalOrder_3194)
      (coe word64ToNat)
