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

module MAlonzo.Code.Function.Properties.Inverse where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Function.Consequences.Setoid qualified
import MAlonzo.Code.Function.Construct.Composition qualified
import MAlonzo.Code.Function.Construct.Identity qualified
import MAlonzo.Code.Function.Construct.Symmetry qualified
import MAlonzo.Code.Function.Properties.RightInverse qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Properties.Inverse.isEquivalence
d_isEquivalence_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_32 ~v0 ~v1 = du_isEquivalence_32
du_isEquivalence_32 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_32
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (coe
         (\ v0 ->
            coe MAlonzo.Code.Function.Construct.Identity.du_inverse_796))
      (\ v0 v1 v2 ->
         coe MAlonzo.Code.Function.Construct.Symmetry.du_inverse_1052 v2)
      (\ v0 v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Function.Construct.Composition.du_inverse_2210 v3 v4)
-- Function.Properties.Inverse.↔-refl
d_'8596''45'refl_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8596''45'refl_36 ~v0 ~v1 = du_'8596''45'refl_36
du_'8596''45'refl_36 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8596''45'refl_36
  = coe MAlonzo.Code.Function.Construct.Identity.du_'8596''45'id_820
-- Function.Properties.Inverse.↔-sym
d_'8596''45'sym_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8596''45'sym_38 ~v0 ~v1 ~v2 ~v3 = du_'8596''45'sym_38
du_'8596''45'sym_38 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8596''45'sym_38
  = coe
      MAlonzo.Code.Function.Construct.Symmetry.du_'8596''45'sym_1148
-- Function.Properties.Inverse.↔-trans
d_'8596''45'trans_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8596''45'trans_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8596''45'trans_40
du_'8596''45'trans_40 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8596''45'trans_40
  = coe MAlonzo.Code.Function.Construct.Composition.du_inverse_2210
-- Function.Properties.Inverse.↔-isEquivalence
d_'8596''45'isEquivalence_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8596''45'isEquivalence_42 ~v0 = du_'8596''45'isEquivalence_42
du_'8596''45'isEquivalence_42 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_'8596''45'isEquivalence_42
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (\ v0 -> coe du_'8596''45'refl_36)
      (coe (\ v0 v1 -> coe du_'8596''45'sym_38))
      (coe (\ v0 v1 v2 -> coe du_'8596''45'trans_40))
-- Function.Properties.Inverse.toFunction
d_toFunction_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_toFunction_44 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_toFunction_44 v6
du_toFunction_44 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
du_toFunction_44 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_Func'46'constructor_6307
      (coe MAlonzo.Code.Function.Bundles.d_to_1972 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1976 (coe v0))
-- Function.Properties.Inverse.fromFunction
d_fromFunction_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_fromFunction_130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_fromFunction_130 v6
du_fromFunction_130 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
du_fromFunction_130 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_Func'46'constructor_6307
      (coe MAlonzo.Code.Function.Bundles.d_from_1974 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1978 (coe v0))
-- Function.Properties.Inverse.Inverse⇒Injection
d_Inverse'8658'Injection_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
d_Inverse'8658'Injection_216 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_Inverse'8658'Injection_216 v2 v5 v6
du_Inverse'8658'Injection_216 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
du_Inverse'8658'Injection_216 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Bundles.C_Injection'46'constructor_8675
      (coe MAlonzo.Code.Function.Bundles.d_to_1972 (coe v2))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1976 (coe v2))
      (coe
         MAlonzo.Code.Function.Consequences.Setoid.du_inverse'691''8658'injective_76
         v0 v1 (MAlonzo.Code.Function.Bundles.d_from_1974 (coe v2))
         (MAlonzo.Code.Function.Bundles.d_to_1972 (coe v2))
         (coe MAlonzo.Code.Function.Bundles.du_inverse'691'_1984 (coe v2)))
-- Function.Properties.Inverse.Inverse⇒Surjection
d_Inverse'8658'Surjection_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d_Inverse'8658'Surjection_328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_Inverse'8658'Surjection_328 v6
du_Inverse'8658'Surjection_328 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
du_Inverse'8658'Surjection_328 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_Surjection'46'constructor_11197
      (coe MAlonzo.Code.Function.Bundles.d_to_1972 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1976 (coe v0))
      (coe
         MAlonzo.Code.Function.Consequences.Setoid.du_inverse'737''8658'surjective_72
         (MAlonzo.Code.Function.Bundles.d_from_1974 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.du_inverse'737'_1982 (coe v0)))
-- Function.Properties.Inverse.Inverse⇒Bijection
d_Inverse'8658'Bijection_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d_Inverse'8658'Bijection_440 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_Inverse'8658'Bijection_440 v2 v5 v6
du_Inverse'8658'Bijection_440 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
du_Inverse'8658'Bijection_440 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Bundles.C_Bijection'46'constructor_15277
      (coe MAlonzo.Code.Function.Bundles.d_to_1972 (coe v2))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1976 (coe v2))
      (coe
         MAlonzo.Code.Function.Consequences.Setoid.du_inverse'7495''8658'bijective_80
         v0 v1 (MAlonzo.Code.Function.Bundles.d_to_1972 (coe v2))
         (MAlonzo.Code.Function.Bundles.d_from_1974 (coe v2))
         (MAlonzo.Code.Function.Bundles.d_inverse_1980 (coe v2)))
-- Function.Properties.Inverse.Inverse⇒Equivalence
d_Inverse'8658'Equivalence_552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_Inverse'8658'Equivalence_552 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_Inverse'8658'Equivalence_552 v6
du_Inverse'8658'Equivalence_552 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_Inverse'8658'Equivalence_552 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_Equivalence'46'constructor_25797
      (coe MAlonzo.Code.Function.Bundles.d_to_1972 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from_1974 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1976 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1978 (coe v0))
-- Function.Properties.Inverse.↔⇒⟶
d_'8596''8658''10230'_638 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_'8596''8658''10230'_638 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''10230'_638
du_'8596''8658''10230'_638 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
du_'8596''8658''10230'_638 = coe du_toFunction_44
-- Function.Properties.Inverse.↔⇒⟵
d_'8596''8658''10229'_640 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_'8596''8658''10229'_640 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''10229'_640
du_'8596''8658''10229'_640 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
du_'8596''8658''10229'_640 = coe du_fromFunction_130
-- Function.Properties.Inverse.↔⇒↣
d_'8596''8658''8611'_642 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
d_'8596''8658''8611'_642 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''8611'_642
du_'8596''8658''8611'_642 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
du_'8596''8658''8611'_642
  = coe
      du_Inverse'8658'Injection_216
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
-- Function.Properties.Inverse.↔⇒↠
d_'8596''8658''8608'_644 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d_'8596''8658''8608'_644 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''8608'_644
du_'8596''8658''8608'_644 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
du_'8596''8658''8608'_644 = coe du_Inverse'8658'Surjection_328
-- Function.Properties.Inverse.↔⇒⤖
d_'8596''8658''10518'_646 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d_'8596''8658''10518'_646 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''10518'_646
du_'8596''8658''10518'_646 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
du_'8596''8658''10518'_646
  = coe
      du_Inverse'8658'Bijection_440
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
-- Function.Properties.Inverse.↔⇒⇔
d_'8596''8658''8660'_648 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_'8596''8658''8660'_648 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''8660'_648
du_'8596''8658''8660'_648 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_'8596''8658''8660'_648 = coe du_Inverse'8658'Equivalence_552
-- Function.Properties.Inverse.↔⇒↩
d_'8596''8658''8617'_650 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d_'8596''8658''8617'_650 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''8617'_650
du_'8596''8658''8617'_650 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
du_'8596''8658''8617'_650
  = coe MAlonzo.Code.Function.Bundles.du_leftInverse_1986
-- Function.Properties.Inverse.↔⇒↪
d_'8596''8658''8618'_652 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d_'8596''8658''8618'_652 ~v0 ~v1 ~v2 ~v3
  = du_'8596''8658''8618'_652
du_'8596''8658''8618'_652 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
du_'8596''8658''8618'_652
  = coe MAlonzo.Code.Function.Bundles.du_rightInverse_1988
-- Function.Properties.Inverse.transportVia
d_transportVia_694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 -> ()) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Function.Bundles.T_Inverse_1960 -> AgdaAny) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Inverse_1960 -> AgdaAny
d_transportVia_694 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 ~v12 v13
                   v14 v15 v16 v17
  = du_transportVia_694
      v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v13 v14 v15 v16 v17
du_transportVia_694 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Function.Bundles.T_Inverse_1960 -> AgdaAny) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Inverse_1960 -> AgdaAny
du_transportVia_694 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
                    v14 v15 v16
  = coe
      v12 v0 v3 v9 v1 v4 v10 v2 v5 v11 (coe v13 v0 v3 v1 v4 v2 v5 v14)
      (coe
         v12 v3 v6 v9 v4 v7 v10 v5 v8 v11 v15
         (coe v13 v6 v9 v7 v10 v8 v11 v16))
-- Function.Properties.Inverse._.↔-fun
d_'8596''45'fun_716 ::
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
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8596''45'fun_716 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_'8596''45'fun_716 v9 v10
du_'8596''45'fun_716 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8596''45'fun_716 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_1972 v1
              (coe v2 (coe MAlonzo.Code.Function.Bundles.d_from_1974 v0 v3))))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Function.Bundles.d_from_1974 v1
              (coe v2 (coe MAlonzo.Code.Function.Bundles.d_to_1972 v0 v3))))
-- Function.Properties.Inverse._._.Eq₁._≈_
d__'8776'__784 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__784 = erased
-- Function.Properties.Inverse._._.Eq₂._≈_
d__'8776'__808 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__808 = erased
-- Function.Properties.Inverse._.to-from
d_to'45'from_834 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_to'45'from_834 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7 v8
  = du_to'45'from_834 v2 v5 v6 v7 v8
du_to'45'from_834 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_to'45'from_834 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Function.Properties.RightInverse.du_to'45'from_486
      (coe v0) (coe v1)
      (coe MAlonzo.Code.Function.Bundles.du_rightInverse_1988 (coe v2))
      (coe v3) (coe v4)
