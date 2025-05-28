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

module MAlonzo.Code.Data.String.Properties where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.String qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Char.Properties qualified
import MAlonzo.Code.Data.List.Relation.Binary.Lex.Strict qualified
import MAlonzo.Code.Data.List.Relation.Binary.Pointwise qualified
import MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base qualified
import MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Construct.On qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.String.Properties.≈⇒≡
d_'8776''8658''8801'_6 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658''8801'_6 = erased
-- Data.String.Properties.≈-reflexive
d_'8776''45'reflexive_8 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'8776''45'reflexive_8 v0 ~v1 ~v2 = du_'8776''45'reflexive_8 v0
du_'8776''45'reflexive_8 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'8776''45'reflexive_8 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_'8801''8658'Pointwise'45''8801'_590
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
-- Data.String.Properties.≈-refl
d_'8776''45'refl_10 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'8776''45'refl_10 v0 = coe du_'8776''45'reflexive_8 (coe v0)
-- Data.String.Properties.≈-sym
d_'8776''45'sym_14 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'8776''45'sym_14 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_symmetric_40
      erased
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
         (\ v2 v3 -> v2) v0 v1)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v2 v3 -> v3)
         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0 v1)
-- Data.String.Properties.≈-trans
d_'8776''45'trans_16 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'8776''45'trans_16 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_transitive_50
      erased
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12
         (\ v3 v4 -> v3) v0 v1)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v3 v4 -> v4)
         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0 v1)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v3 v4 -> v4)
         MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1 v2)
-- Data.String.Properties.≈-subst
d_'8776''45'subst_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 -> ()) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  AgdaAny -> AgdaAny
d_'8776''45'subst_20 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8776''45'subst_20 v5
du_'8776''45'subst_20 :: AgdaAny -> AgdaAny
du_'8776''45'subst_20 v0 = coe v0
-- Data.String.Properties._≈?_
d__'8776''63'__28 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8776''63'__28 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_decidable_112
      (coe MAlonzo.Code.Data.Char.Properties.d__'8799'__14)
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1)
-- Data.String.Properties.≈-isEquivalence
d_'8776''45'isEquivalence_34 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_34
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (coe d_'8776''45'refl_10) (coe d_'8776''45'sym_14)
      (coe d_'8776''45'trans_16)
-- Data.String.Properties.≈-setoid
d_'8776''45'setoid_48 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8776''45'setoid_48
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_733
      d_'8776''45'isEquivalence_34
-- Data.String.Properties.≈-isDecEquivalence
d_'8776''45'isDecEquivalence_50 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_'8776''45'isDecEquivalence_50
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecEquivalence'46'constructor_3083
      (coe d_'8776''45'isEquivalence_34) (coe d__'8776''63'__28)
-- Data.String.Properties.≈-decSetoid
d_'8776''45'decSetoid_52 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_'8776''45'decSetoid_52
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecSetoid'46'constructor_1389
      d_'8776''45'isDecEquivalence_50
-- Data.String.Properties._≟_
d__'8799'__54 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__54 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
      erased (\ v2 -> coe du_'8776''45'reflexive_8 (coe v0))
      (coe d__'8776''63'__28 (coe v0) (coe v1))
-- Data.String.Properties.≡-setoid
d_'8801''45'setoid_60 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8801''45'setoid_60
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.String.Properties.≡-decSetoid
d_'8801''45'decSetoid_62 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_'8801''45'decSetoid_62
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
      (coe d__'8799'__54)
-- Data.String.Properties._<?_
d__'60''63'__64 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__64 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Lex.Strict.du_'60''45'decidable_274
      MAlonzo.Code.Data.Char.Properties.d__'8799'__14
      MAlonzo.Code.Data.Char.Properties.d__'60''63'__44
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v1)
-- Data.String.Properties.<-isStrictPartialOrder-≈
d_'60''45'isStrictPartialOrder'45''8776'_70 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''45'isStrictPartialOrder'45''8776'_70
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_isStrictPartialOrder_372
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.Strict.du_'60''45'isStrictPartialOrder_278
         (coe
            MAlonzo.Code.Data.Char.Properties.d_'60''45'isStrictPartialOrder_102))
-- Data.String.Properties.<-isStrictTotalOrder-≈
d_'60''45'isStrictTotalOrder'45''8776'_72 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''45'isStrictTotalOrder'45''8776'_72
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_isStrictTotalOrder_526
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.Strict.du_'60''45'isStrictTotalOrder_314
         (coe
            MAlonzo.Code.Data.Char.Properties.d_'60''45'isStrictTotalOrder_118))
-- Data.String.Properties.<-strictPartialOrder-≈
d_'60''45'strictPartialOrder'45''8776'_74 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_'60''45'strictPartialOrder'45''8776'_74
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_strictPartialOrder_622
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.Strict.du_'60''45'strictPartialOrder_374
         (coe
            MAlonzo.Code.Data.Char.Properties.d_'60''45'strictPartialOrder_120))
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12)
-- Data.String.Properties.<-strictTotalOrder-≈
d_'60''45'strictTotalOrder'45''8776'_76 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
d_'60''45'strictTotalOrder'45''8776'_76
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_strictTotalOrder_646
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.Strict.du_'60''45'strictTotalOrder_442
         (coe
            MAlonzo.Code.Data.Char.Properties.d_'60''45'strictTotalOrder_122))
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12)
-- Data.String.Properties.≤-isDecPartialOrder-≈
d_'8804''45'isDecPartialOrder'45''8776'_78 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
d_'8804''45'isDecPartialOrder'45''8776'_78
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_isDecPartialOrder_314
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.Strict.du_'8804''45'isDecPartialOrder_726
         (coe
            MAlonzo.Code.Data.Char.Properties.d_'60''45'isStrictTotalOrder_118))
-- Data.String.Properties.≤-isDecTotalOrder-≈
d_'8804''45'isDecTotalOrder'45''8776'_80 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
d_'8804''45'isDecTotalOrder'45''8776'_80
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_isDecTotalOrder_460
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.Strict.du_'8804''45'isDecTotalOrder_834
         (coe
            MAlonzo.Code.Data.Char.Properties.d_'60''45'isStrictTotalOrder_118))
-- Data.String.Properties.≤-decTotalOrder-≈
d_'8804''45'decTotalOrder'45''8776'_82 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
d_'8804''45'decTotalOrder'45''8776'_82
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_decTotalOrder_638
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.Strict.du_'8804''45'decTotalOrder_1130
         (coe
            MAlonzo.Code.Data.Char.Properties.d_'60''45'strictTotalOrder_122))
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12)
-- Data.String.Properties.≤-decPoset-≈
d_'8804''45'decPoset'45''8776'_84 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecPoset_406
d_'8804''45'decPoset'45''8776'_84
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_decPoset_614
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Lex.Strict.du_'8804''45'decPoset_1038
         (coe
            MAlonzo.Code.Data.Char.Properties.d_'60''45'strictTotalOrder_122))
      (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12)
-- Data.String.Properties._==_
d__'61''61'__86 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d__'61''61'__86 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_122
      (coe d__'8799'__54 (coe v0) (coe v1))
