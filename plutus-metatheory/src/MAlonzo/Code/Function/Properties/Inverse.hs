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

module MAlonzo.Code.Function.Properties.Inverse where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Function.Consequences.Setoid
import qualified MAlonzo.Code.Function.Construct.Composition
import qualified MAlonzo.Code.Function.Construct.Identity
import qualified MAlonzo.Code.Function.Construct.Symmetry
import qualified MAlonzo.Code.Function.Properties.RightInverse
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Function.Properties.Inverse.isEquivalence
d_isEquivalence_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_32 ~v0 ~v1 = du_isEquivalence_32
du_isEquivalence_32 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_32
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_46
      (coe
         (\ v0 ->
            coe MAlonzo.Code.Function.Construct.Identity.du_inverse_636))
      (\ v0 v1 v2 ->
         coe MAlonzo.Code.Function.Construct.Symmetry.du_inverse_1096 v2)
      (\ v0 v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Function.Construct.Composition.du_inverse_2322 v3 v4)
-- Function.Properties.Inverse.↔-refl
d_'8596''45'refl_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'8596''45'refl_36 ~v0 ~v1 = du_'8596''45'refl_36
du_'8596''45'refl_36 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'8596''45'refl_36
  = coe MAlonzo.Code.Function.Construct.Identity.du_'8596''45'id_660
-- Function.Properties.Inverse.↔-sym
d_'8596''45'sym_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'8596''45'sym_38 ~v0 ~v1 ~v2 ~v3 = du_'8596''45'sym_38
du_'8596''45'sym_38 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'8596''45'sym_38
  = coe
      MAlonzo.Code.Function.Construct.Symmetry.du_'8596''45'sym_1196
-- Function.Properties.Inverse.↔-trans
d_'8596''45'trans_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'8596''45'trans_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8596''45'trans_40
du_'8596''45'trans_40 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'8596''45'trans_40
  = coe MAlonzo.Code.Function.Construct.Composition.du_inverse_2322
-- Function.Properties.Inverse.↔-isEquivalence
d_'8596''45'isEquivalence_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8596''45'isEquivalence_42 ~v0 = du_'8596''45'isEquivalence_42
du_'8596''45'isEquivalence_42 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_'8596''45'isEquivalence_42
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_46
      (\ v0 -> coe du_'8596''45'refl_36)
      (coe (\ v0 v1 -> coe du_'8596''45'sym_38))
      (coe (\ v0 v1 v2 -> coe du_'8596''45'trans_40))
-- Function.Properties.Inverse.toFunction
d_toFunction_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
d_toFunction_44 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_toFunction_44 v6
du_toFunction_44 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
du_toFunction_44 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_840
      (coe MAlonzo.Code.Function.Bundles.d_to_2134 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_2138 (coe v0))
-- Function.Properties.Inverse.fromFunction
d_fromFunction_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
d_fromFunction_134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_fromFunction_134 v6
du_fromFunction_134 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
du_fromFunction_134 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_840
      (coe MAlonzo.Code.Function.Bundles.d_from_2136 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_2140 (coe v0))
-- Function.Properties.Inverse.Inverse⇒Injection
d_Inverse'8658'Injection_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842
d_Inverse'8658'Injection_224 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_Inverse'8658'Injection_224 v2 v5 v6
du_Inverse'8658'Injection_224 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842
du_Inverse'8658'Injection_224 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_916
      (coe MAlonzo.Code.Function.Bundles.d_to_2134 (coe v2))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_2138 (coe v2))
      (coe
         MAlonzo.Code.Function.Consequences.Setoid.du_inverse'691''8658'injective_80
         v0 v1 (MAlonzo.Code.Function.Bundles.d_from_2136 (coe v2))
         (MAlonzo.Code.Function.Bundles.d_to_2134 (coe v2))
         (coe MAlonzo.Code.Function.Bundles.du_inverse'691'_2146 (coe v2)))
-- Function.Properties.Inverse.Inverse⇒Surjection
d_Inverse'8658'Surjection_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
d_Inverse'8658'Surjection_326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_Inverse'8658'Surjection_326 v6
du_Inverse'8658'Surjection_326 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
du_Inverse'8658'Surjection_326 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_1002
      (coe MAlonzo.Code.Function.Bundles.d_to_2134 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_2138 (coe v0))
      (coe
         MAlonzo.Code.Function.Consequences.Setoid.du_inverse'737''8658'surjective_76
         (MAlonzo.Code.Function.Bundles.d_from_2136 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.du_inverse'737'_2144 (coe v0)))
-- Function.Properties.Inverse.Inverse⇒Bijection
d_Inverse'8658'Bijection_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004
d_Inverse'8658'Bijection_428 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_Inverse'8658'Bijection_428 v2 v5 v6
du_Inverse'8658'Bijection_428 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004
du_Inverse'8658'Bijection_428 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_1094
      (coe MAlonzo.Code.Function.Bundles.d_to_2134 (coe v2))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_2138 (coe v2))
      (coe
         MAlonzo.Code.Function.Consequences.Setoid.du_inverse'7495''8658'bijective_84
         v0 v1 (MAlonzo.Code.Function.Bundles.d_to_2134 (coe v2))
         (MAlonzo.Code.Function.Bundles.d_from_2136 (coe v2))
         (MAlonzo.Code.Function.Bundles.d_inverse_2142 (coe v2)))
-- Function.Properties.Inverse.Inverse⇒Equivalence
d_Inverse'8658'Equivalence_530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_Inverse'8658'Equivalence_530 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_Inverse'8658'Equivalence_530 v6
du_Inverse'8658'Equivalence_530 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_Inverse'8658'Equivalence_530 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_1940
      (coe MAlonzo.Code.Function.Bundles.d_to_2134 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from_2136 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_2138 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_2140 (coe v0))
-- Function.Properties.Inverse.↔⇒⟶
d_'8596''8658''10230'_620 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
d_'8596''8658''10230'_620 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''10230'_620
du_'8596''8658''10230'_620 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
du_'8596''8658''10230'_620 = coe du_toFunction_44
-- Function.Properties.Inverse.↔⇒⟵
d_'8596''8658''10229'_622 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
d_'8596''8658''10229'_622 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''10229'_622
du_'8596''8658''10229'_622 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
du_'8596''8658''10229'_622 = coe du_fromFunction_134
-- Function.Properties.Inverse.↔⇒↣
d_'8596''8658''8611'_624 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842
d_'8596''8658''8611'_624 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''8611'_624
du_'8596''8658''8611'_624 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842
du_'8596''8658''8611'_624
  = coe
      du_Inverse'8658'Injection_224
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
-- Function.Properties.Inverse.↔⇒↠
d_'8596''8658''8608'_626 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
d_'8596''8658''8608'_626 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''8608'_626
du_'8596''8658''8608'_626 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
du_'8596''8658''8608'_626 = coe du_Inverse'8658'Surjection_326
-- Function.Properties.Inverse.↔⇒⤖
d_'8596''8658''10518'_628 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004
d_'8596''8658''10518'_628 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''10518'_628
du_'8596''8658''10518'_628 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004
du_'8596''8658''10518'_628
  = coe
      du_Inverse'8658'Bijection_428
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
-- Function.Properties.Inverse.↔⇒⇔
d_'8596''8658''8660'_630 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_'8596''8658''8660'_630 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''8660'_630
du_'8596''8658''8660'_630 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_'8596''8658''8660'_630 = coe du_Inverse'8658'Equivalence_530
-- Function.Properties.Inverse.↔⇒↩
d_'8596''8658''8617'_632 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
d_'8596''8658''8617'_632 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''8617'_632
du_'8596''8658''8617'_632 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
du_'8596''8658''8617'_632
  = coe MAlonzo.Code.Function.Bundles.du_leftInverse_2148
-- Function.Properties.Inverse.↔⇒↪
d_'8596''8658''8618'_634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
d_'8596''8658''8618'_634 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''8618'_634
du_'8596''8658''8618'_634 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
du_'8596''8658''8618'_634
  = coe MAlonzo.Code.Function.Bundles.du_rightInverse_2150
-- Function.Properties.Inverse.transportVia
d_transportVia_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 -> ()) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
   MAlonzo.Code.Function.Bundles.T_Inverse_2122 -> AgdaAny) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Inverse_2122 -> AgdaAny
d_transportVia_676 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 v13
                   v14 v15 v16 v17
  = du_transportVia_676
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v13 v14 v15 v16 v17
du_transportVia_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
   MAlonzo.Code.Function.Bundles.T_Inverse_2122 -> AgdaAny) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Inverse_2122 -> AgdaAny
du_transportVia_676 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16
  = coe
      v12 v0 v3 v9 v1 v4 v10 v2 v5 v11 (coe v13 v0 v3 v1 v4 v2 v5 v14)
      (coe
         v12 v3 v6 v9 v4 v7 v10 v5 v8 v11 v15
         (coe v13 v6 v9 v7 v10 v8 v11 v16))
-- Function.Properties.Inverse._.↔-fun
d_'8596''45'fun_698 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   () ->
   (AgdaAny -> ()) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> AgdaAny) ->
   (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'8596''45'fun_698 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_'8596''45'fun_698 v9 v10
du_'8596''45'fun_698 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'8596''45'fun_698 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2542
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_2134 v1
              (coe v2 (coe MAlonzo.Code.Function.Bundles.d_from_2136 v0 v3))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Function.Bundles.d_from_2136 v1
              (coe v2 (coe MAlonzo.Code.Function.Bundles.d_to_2134 v0 v3))))
-- Function.Properties.Inverse._._.Eq₁._≈_
d__'8776'__766 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__766 = erased
-- Function.Properties.Inverse._._.Eq₂._≈_
d__'8776'__792 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__792 = erased
-- Function.Properties.Inverse._.to-from
d_to'45'from_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'from_820 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8
  = du_to'45'from_820 v2 v5 v6 v7 v8
du_to'45'from_820 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_to'45'from_820 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Function.Properties.RightInverse.du_to'45'from_510
      (coe v0) (coe v1)
      (coe MAlonzo.Code.Function.Bundles.du_rightInverse_2150 (coe v2))
      (coe v3) (coe v4)
