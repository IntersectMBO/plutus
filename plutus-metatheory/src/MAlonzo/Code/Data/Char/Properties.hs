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

module MAlonzo.Code.Data.Char.Properties where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Char qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Nat.Base qualified
import MAlonzo.Code.Data.Nat.Properties qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive qualified
import MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.Properties qualified
import MAlonzo.Code.Relation.Binary.Construct.On qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Char.Properties.≈⇒≡
d_'8776''8658''8801'_6 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8658''8801'_6 = erased
-- Data.Char.Properties.≉⇒≢
d_'8777''8658''8802'_8 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8777''8658''8802'_8 = erased
-- Data.Char.Properties.≈-reflexive
d_'8776''45'reflexive_12 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''45'reflexive_12 = erased
-- Data.Char.Properties._≟_
d__'8799'__14 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__14 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
      erased erased
      (coe
         MAlonzo.Code.Data.Nat.Properties.d__'8799'__2688
         (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0)
         (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v1))
-- Data.Char.Properties.setoid
d_setoid_20 :: MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_20
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402
-- Data.Char.Properties.decSetoid
d_decSetoid_22 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_decSetoid_22
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_decSetoid_406
      (coe d__'8799'__14)
-- Data.Char.Properties.isDecEquivalence
d_isDecEquivalence_24 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_isDecEquivalence_24
  = coe
      MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isDecEquivalence_398
      (coe d__'8799'__14)
-- Data.Char.Properties._==_
d__'61''61'__26 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> Bool
d__'61''61'__26 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_122
      (coe d__'8799'__14 (coe v0) (coe v1))
-- Data.Char.Properties._<?_
d__'60''63'__44 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__44
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_decidable_102
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28)
      (coe MAlonzo.Code.Data.Nat.Properties.d__'60''63'__3030)
-- Data.Char.Properties.<-cmp
d_'60''45'cmp_46 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''45'cmp_46 v0 v1
  = let v2
          = coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0 in
    coe
      (let v3
             = coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v1 in
       coe
         (let v4
                = coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                    erased
                    (\ v4 ->
                       coe
                         MAlonzo.Code.Data.Nat.Properties.du_'8801''8658''8801''7495'_2678
                         (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0))
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                       (coe
                          eqInt (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0)
                          (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v1))
                       (coe
                          MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_66
                          (coe
                             eqInt (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0)
                             (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v1)))) in
          coe
            (case coe v4 of
               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                 -> if coe v5
                      then case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v7
                               -> coe MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v7
                             _ -> MAlonzo.RTE.mazUnreachableError
                      else coe
                             seq (coe v6)
                             (let v7
                                    = ltInt
                                        (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v1) in
                              coe
                                (if coe v7
                                   then coe
                                          seq
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_66
                                             (coe v7))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.du_'60''7495''8658''60'_2716
                                                (coe v2)))
                                   else coe
                                          seq
                                          (coe
                                             MAlonzo.Code.Relation.Nullary.Reflects.d_T'45'reflects_66
                                             (coe v7))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                                             (coe
                                                MAlonzo.Code.Data.Nat.Properties.du_'8804''8743''8802''8658''60'_2918
                                                (coe v2)
                                                (coe
                                                   MAlonzo.Code.Data.Nat.Properties.du_'8814''8658''8805'_2902
                                                   (coe v2) (coe v3))))))
               _ -> MAlonzo.RTE.mazUnreachableError)))
-- Data.Char.Properties.<-irrefl
d_'60''45'irrefl_86 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_86 = erased
-- Data.Char.Properties.<-trans
d_'60''45'trans_88 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_'60''45'trans_88 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_transitive_64
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28)
      (\ v3 v4 v5 v6 v7 ->
         coe
           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_2980 v4 v6 v7)
      (coe v0) (coe v1) (coe v2)
-- Data.Char.Properties.<-asym
d_'60''45'asym_96 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'asym_96 = erased
-- Data.Char.Properties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_102 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''45'isStrictPartialOrder_102
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_14045
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      d_'60''45'trans_88
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4)))
-- Data.Char.Properties.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_118 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''45'isStrictTotalOrder_118
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_24953
      (coe d_'60''45'isStrictPartialOrder_102) (coe d_'60''45'cmp_46)
-- Data.Char.Properties.<-strictPartialOrder
d_'60''45'strictPartialOrder_120 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_'60''45'strictPartialOrder_120
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictPartialOrder'46'constructor_11097
      d_'60''45'isStrictPartialOrder_102
-- Data.Char.Properties.<-strictTotalOrder
d_'60''45'strictTotalOrder_122 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
d_'60''45'strictTotalOrder_122
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictTotalOrder'46'constructor_21059
      d_'60''45'isStrictTotalOrder_118
-- Data.Char.Properties._≤?_
d__'8804''63'__124 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__124
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.Properties.du_decidable_184
      (coe d_'60''45'cmp_46)
-- Data.Char.Properties.≤-reflexive
d_'8804''45'reflexive_126 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30
d_'8804''45'reflexive_126 ~v0 ~v1 = du_'8804''45'reflexive_126
du_'8804''45'reflexive_126 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30
du_'8804''45'reflexive_126 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.du_reflexive_72
-- Data.Char.Properties.≤-trans
d_'8804''45'trans_128 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30
d_'8804''45'trans_128 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.Properties.du_trans_94
      (coe d_'60''45'trans_88) (coe v0) (coe v1) (coe v2)
-- Data.Char.Properties.≤-antisym
d_'8804''45'antisym_136 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Relation.Binary.Construct.Closure.Reflexive.T_ReflClosure_30 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'antisym_136 = erased
-- Data.Char.Properties.≤-isPreorder
d_'8804''45'isPreorder_138 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8804''45'isPreorder_138
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 -> coe du_'8804''45'reflexive_126)
      (coe d_'8804''45'trans_128)
-- Data.Char.Properties.≤-isPartialOrder
d_'8804''45'isPartialOrder_140 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_'8804''45'isPartialOrder_140
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_9853
      (coe d_'8804''45'isPreorder_138) erased
-- Data.Char.Properties.≤-isDecPartialOrder
d_'8804''45'isDecPartialOrder_142 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
d_'8804''45'isDecPartialOrder_142
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecPartialOrder'46'constructor_11683
      (coe d_'8804''45'isPartialOrder_140) (coe d__'8799'__14)
      (coe d__'8804''63'__124)
-- Data.Char.Properties.≤-preorder
d_'8804''45'preorder_144 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_'8804''45'preorder_144
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2267
      d_'8804''45'isPreorder_138
-- Data.Char.Properties.≤-poset
d_'8804''45'poset_146 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_'8804''45'poset_146
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_6389
      d_'8804''45'isPartialOrder_140
-- Data.Char.Properties.≤-decPoset
d_'8804''45'decPoset_148 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecPoset_406
d_'8804''45'decPoset_148
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecPoset'46'constructor_8213
      d_'8804''45'isDecPartialOrder_142
-- Data.Char.Properties.≈-refl
d_'8776''45'refl_150 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''45'refl_150 = erased
-- Data.Char.Properties.≈-sym
d_'8776''45'sym_152 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''45'sym_152 = erased
-- Data.Char.Properties.≈-trans
d_'8776''45'trans_154 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''45'trans_154 = erased
-- Data.Char.Properties.≈-subst
d_'8776''45'subst_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.Char.T_Char_6 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_'8776''45'subst_158 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8776''45'subst_158 v5
du_'8776''45'subst_158 :: AgdaAny -> AgdaAny
du_'8776''45'subst_158 v0 = coe v0
-- Data.Char.Properties._≈?_
d__'8776''63'__166 ::
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Agda.Builtin.Char.T_Char_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8776''63'__166 v0 v1
  = coe
      MAlonzo.Code.Data.Nat.Properties.d__'8799'__2688
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v0)
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28 v1)
-- Data.Char.Properties.≈-isEquivalence
d_'8776''45'isEquivalence_172 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''45'isEquivalence_172
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      erased erased erased
-- Data.Char.Properties.≈-setoid
d_'8776''45'setoid_174 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8776''45'setoid_174
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_733
      d_'8776''45'isEquivalence_172
-- Data.Char.Properties.≈-isDecEquivalence
d_'8776''45'isDecEquivalence_176 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_'8776''45'isDecEquivalence_176
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecEquivalence'46'constructor_3083
      (coe d_'8776''45'isEquivalence_172) (coe d__'8776''63'__166)
-- Data.Char.Properties.≈-decSetoid
d_'8776''45'decSetoid_178 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_'8776''45'decSetoid_178
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecSetoid'46'constructor_1389
      d_'8776''45'isDecEquivalence_176
-- Data.Char.Properties.≡-setoid
d_'8801''45'setoid_180 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8801''45'setoid_180 = coe d_setoid_20
-- Data.Char.Properties.≡-decSetoid
d_'8801''45'decSetoid_182 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_'8801''45'decSetoid_182 = coe d_decSetoid_22
-- Data.Char.Properties.<-isStrictPartialOrder-≈
d_'60''45'isStrictPartialOrder'45''8776'_184 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''45'isStrictPartialOrder'45''8776'_184
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_isStrictPartialOrder_372
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'60''45'isStrictPartialOrder_3046)
-- Data.Char.Properties.<-isStrictTotalOrder-≈
d_'60''45'isStrictTotalOrder'45''8776'_186 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''45'isStrictTotalOrder'45''8776'_186
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_isStrictTotalOrder_526
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28)
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'60''45'isStrictTotalOrder_3048)
-- Data.Char.Properties.<-strictPartialOrder-≈
d_'60''45'strictPartialOrder'45''8776'_188 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_'60''45'strictPartialOrder'45''8776'_188
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_strictPartialOrder_622
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'60''45'strictPartialOrder_3050)
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28)
-- Data.Char.Properties.<-strictTotalOrder-≈
d_'60''45'strictTotalOrder'45''8776'_190 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
d_'60''45'strictTotalOrder'45''8776'_190
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_strictTotalOrder_646
      (coe
         MAlonzo.Code.Data.Nat.Properties.d_'60''45'strictTotalOrder_3052)
      (coe MAlonzo.Code.Agda.Builtin.Char.d_primCharToNat_28)
