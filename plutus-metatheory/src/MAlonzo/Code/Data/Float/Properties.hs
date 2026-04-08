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

module MAlonzo.Code.Data.Float.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Float
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Maybe.Properties
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.On
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.Float.Properties.≈⇒≡
d_'8776''8658''8801'_6 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658''8801'_6 = erased
-- Data.Float.Properties.≈-reflexive
d_'8776''45'reflexive_10 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''45'reflexive_10 = erased
-- Data.Float.Properties.≈-refl
d_'8776''45'refl_14 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''45'refl_14 = erased
-- Data.Float.Properties.≈-sym
d_'8776''45'sym_16 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''45'sym_16 = erased
-- Data.Float.Properties.≈-trans
d_'8776''45'trans_18 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''45'trans_18 = erased
-- Data.Float.Properties.≈-subst
d_'8776''45'subst_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.Float.T_Float_6 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_'8776''45'subst_22 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8776''45'subst_22 v5
du_'8776''45'subst_22 :: AgdaAny -> AgdaAny
du_'8776''45'subst_22 v0 = coe v0
-- Data.Float.Properties._≈?_
d__'8776''63'__30 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8776''63'__30
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_decidable_102
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Data.Maybe.Base.du_map_64 word64ToNat
              (coe MAlonzo.Code.Agda.Builtin.Float.d_primFloatToWord64_22 v0)))
      (coe
         MAlonzo.Code.Data.Maybe.Properties.du_'8801''45'dec_24
         (coe MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796))
-- Data.Float.Properties.≈-isEquivalence
d_'8776''45'isEquivalence_32 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''45'isEquivalence_32
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_46 erased
      erased erased
-- Data.Float.Properties.≈-setoid
d_'8776''45'setoid_46 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'8776''45'setoid_46
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      d_'8776''45'isEquivalence_32
-- Data.Float.Properties.≈-isDecEquivalence
d_'8776''45'isDecEquivalence_48 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_'8776''45'isDecEquivalence_48
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_70
      (coe d_'8776''45'isEquivalence_32) (coe d__'8776''63'__30)
-- Data.Float.Properties.≈-decSetoid
d_'8776''45'decSetoid_50 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_'8776''45'decSetoid_50
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_134
      d_'8776''45'isDecEquivalence_48
-- Data.Float.Properties._≟_
d__'8799'__52 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__52 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      erased erased (coe d__'8776''63'__30 v0 v1)
-- Data.Float.Properties.≡-setoid
d_'8801''45'setoid_58 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'8801''45'setoid_58
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Float.Properties.≡-decSetoid
d_'8801''45'decSetoid_60 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_'8801''45'decSetoid_60
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
      (coe d__'8799'__52)
-- Data.Float.Properties.toWord-injective
d_toWord'45'injective_62 ::
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Float.T_Float_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_toWord'45'injective_62 = erased
