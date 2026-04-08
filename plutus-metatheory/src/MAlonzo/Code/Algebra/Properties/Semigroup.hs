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

module MAlonzo.Code.Algebra.Properties.Semigroup where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Consequences.Base
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Properties.Semigroup._.Alternative
d_Alternative_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Alternative_38 = erased
-- Algebra.Properties.Semigroup._.Flexible
d_Flexible_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Flexible_40 = erased
-- Algebra.Properties.Semigroup._.LeftAlternative
d_LeftAlternative_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftAlternative_42 = erased
-- Algebra.Properties.Semigroup._.RightAlternative
d_RightAlternative_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightAlternative_44 = erased
-- Algebra.Properties.Semigroup.x∙yz≈xy∙z
d_x'8729'yz'8776'xy'8729'z_64 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8729'yz'8776'xy'8729'z_64 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v3))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v1 v2 v3)
-- Algebra.Properties.Semigroup.alternativeˡ
d_alternative'737'_72 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_alternative'737'_72 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_498
      (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v1 v1 v2
-- Algebra.Properties.Semigroup.alternativeʳ
d_alternative'691'_78 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_alternative'691'_78 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v2)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v2))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v1 v2 v2)
-- Algebra.Properties.Semigroup.alternative
d_alternative_84 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_alternative_84 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Algebra.Structures.d_assoc_498
              (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v1 v1
              v2))
      (coe
         (\ v1 v2 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_sym_38
              (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                 (coe
                    MAlonzo.Code.Algebra.Structures.d_isMagma_496
                    (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
              (coe
                 MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
                 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v2)
              (coe
                 MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1
                 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v2))
              (coe
                 MAlonzo.Code.Algebra.Structures.d_assoc_498
                 (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v1 v2
                 v2)))
-- Algebra.Properties.Semigroup.flexible
d_flexible_86 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_flexible_86 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Structures.d_assoc_498
      (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v1 v2 v1
-- Algebra.Properties.Semigroup._.uv≈w⇒xu∙v≈xw
d_uv'8776'w'8658'xu'8729'v'8776'xw_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_uv'8776'w'8658'xu'8729'v'8776'xw_106 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_uv'8776'w'8658'xu'8729'v'8776'xw_106 v2 v3 v4 v5 v6 v7
du_uv'8776'w'8658'xu'8729'v'8776'xw_106 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_uv'8776'w'8658'xu'8729'v'8776'xw_106 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v1) v2)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2))
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v6 v7 -> v7)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v5 v1 v2)
      (coe
         MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
         (MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)))))
         v5 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v3
         v4)
-- Algebra.Properties.Semigroup._.uv≈w⇒u∙vx≈wx
d_uv'8776'w'8658'u'8729'vx'8776'wx_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_uv'8776'w'8658'u'8729'vx'8776'wx_112 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_uv'8776'w'8658'u'8729'vx'8776'wx_112 v2 v3 v4 v5 v6 v7
du_uv'8776'w'8658'u'8729'vx'8776'wx_112 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_uv'8776'w'8658'u'8729'vx'8776'wx_112 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v5))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v5)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v6 v7 -> v7)
         (\ v6 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v5)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v3)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v5)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v5))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_498
            (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v1 v2
            v5))
      (coe
         MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
         (MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)))))
         v5 (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v3
         v4)
-- Algebra.Properties.Semigroup._.uv≈w⇒u[vx∙y]≈w∙xy
d_uv'8776'w'8658'u'91'vx'8729'y'93''8776'w'8729'xy_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_uv'8776'w'8658'u'91'vx'8729'y'93''8776'w'8729'xy_120 ~v0 ~v1 v2
                                                       v3 v4 v5 v6 v7 v8
  = du_uv'8776'w'8658'u'91'vx'8729'y'93''8776'w'8729'xy_120
      v2 v3 v4 v5 v6 v7 v8
du_uv'8776'w'8658'u'91'vx'8729'y'93''8776'w'8729'xy_120 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_uv'8776'w'8658'u'91'vx'8729'y'93''8776'w'8729'xy_120 v0 v1 v2 v3
                                                        v4 v5 v6
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1)
         (\ v7 v8 -> v7)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v5) v6)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v6)))
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v7 v8 -> v8)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v5) v6)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v6)))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v6))
      (coe
         MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
         (MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)))))
         v1
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v5) v6)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v6))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_498
            (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v2 v5
            v6))
      (coe
         du_uv'8776'w'8658'u'8729'vx'8776'wx_112 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v6))
-- Algebra.Properties.Semigroup._.uv≈w⇒x[uv∙y]≈x∙wy
d_uv'8776'w'8658'x'91'uv'8729'y'93''8776'x'8729'wy_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_uv'8776'w'8658'x'91'uv'8729'y'93''8776'x'8729'wy_130 ~v0 ~v1 v2
                                                       v3 v4 v5 v6 v7 v8
  = du_uv'8776'w'8658'x'91'uv'8729'y'93''8776'x'8729'wy_130
      v2 v3 v4 v5 v6 v7 v8
du_uv'8776'w'8658'x'91'uv'8729'y'93''8776'x'8729'wy_130 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_uv'8776'w'8658'x'91'uv'8729'y'93''8776'x'8729'wy_130 v0 v1 v2 v3
                                                        v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
      (MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)))))
      v5
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v6))
      (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v6)
      (coe
         du_uv'8776'w'8658'u'8729'vx'8776'wx_112 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v6))
-- Algebra.Properties.Semigroup._.uv≈w⇒[x∙yu]v≈x∙yw
d_uv'8776'w'8658''91'x'8729'yu'93'v'8776'x'8729'yw_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_uv'8776'w'8658''91'x'8729'yu'93'v'8776'x'8729'yw_140 ~v0 ~v1 v2
                                                       v3 v4 v5 v6 v7 v8
  = du_uv'8776'w'8658''91'x'8729'yu'93'v'8776'x'8729'yw_140
      v2 v3 v4 v5 v6 v7 v8
du_uv'8776'w'8658''91'x'8729'yu'93'v'8776'x'8729'yw_140 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_uv'8776'w'8658''91'x'8729'yu'93'v'8776'x'8729'yw_140 v0 v1 v2 v3
                                                        v4 v5 v6
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v1))
         v2)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v1) v2))
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v7 v8 -> v8)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v1) v2)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v3))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v5
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v1) v2)
      (coe
         MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
         (MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)))))
         v5
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v1) v2)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v3)
         (coe
            du_uv'8776'w'8658'xu'8729'v'8776'xw_106 (coe v0) (coe v1) (coe v2)
            (coe v3) (coe v4) (coe v6)))
-- Algebra.Properties.Semigroup._.uv≈w⇒[xu∙v]y≈x∙wy
d_uv'8776'w'8658''91'xu'8729'v'93'y'8776'x'8729'wy_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_uv'8776'w'8658''91'xu'8729'v'93'y'8776'x'8729'wy_150 ~v0 ~v1 v2
                                                       v3 v4 v5 v6 v7 v8
  = du_uv'8776'w'8658''91'xu'8729'v'93'y'8776'x'8729'wy_150
      v2 v3 v4 v5 v6 v7 v8
du_uv'8776'w'8658''91'xu'8729'v'93'y'8776'x'8729'wy_150 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_uv'8776'w'8658''91'xu'8729'v'93'y'8776'x'8729'wy_150 v0 v1 v2 v3
                                                        v4 v5 v6
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (\ v7 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v7 v6)
         (\ v7 v8 -> v7)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v1) v2)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v3))
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v7 v8 -> v8)
         (\ v7 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v7 v6)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v1) v2)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v3))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v6))
      (coe
         MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
         (MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)))))
         v6
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v1) v2)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v3)
         (coe
            du_uv'8776'w'8658'xu'8729'v'8776'xw_106 (coe v0) (coe v1) (coe v2)
            (coe v3) (coe v4) (coe v5)))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v5 v3 v6)
-- Algebra.Properties.Semigroup._.uv≈w⇒[xy∙u]v≈x∙yw
d_uv'8776'w'8658''91'xy'8729'u'93'v'8776'x'8729'yw_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_uv'8776'w'8658''91'xy'8729'u'93'v'8776'x'8729'yw_160 ~v0 ~v1 v2
                                                       v3 v4 v5 v6 v7 v8
  = du_uv'8776'w'8658''91'xy'8729'u'93'v'8776'x'8729'yw_160
      v2 v3 v4 v5 v6 v7 v8
du_uv'8776'w'8658''91'xy'8729'u'93'v'8776'x'8729'yw_160 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_uv'8776'w'8658''91'xy'8729'u'93'v'8776'x'8729'yw_160 v0 v1 v2 v3
                                                        v4 v5 v6
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (\ v7 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v7 v2)
         (\ v7 v8 -> v7)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v6) v1)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v1)))
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v7 v8 -> v8)
         (\ v7 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v7 v2)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v6) v1)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v1)))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v3))
      (coe
         MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
         (MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)))))
         v2
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v6) v1)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v1))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_498
            (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v5 v6
            v1))
      (coe
         du_uv'8776'w'8658''91'x'8729'yu'93'v'8776'x'8729'yw_140 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Algebra.Properties.Semigroup._.uv≈w⇒xu∙vy≈x∙wy
d_uv'8776'w'8658'xu'8729'vy'8776'x'8729'wy_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_uv'8776'w'8658'xu'8729'vy'8776'x'8729'wy_182 ~v0 ~v1 v2 v3 v4 v5
                                               v6 v7 v8
  = du_uv'8776'w'8658'xu'8729'vy'8776'x'8729'wy_182
      v2 v3 v4 v5 v6 v7 v8
du_uv'8776'w'8658'xu'8729'vy'8776'x'8729'wy_182 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_uv'8776'w'8658'xu'8729'vy'8776'x'8729'wy_182 v0 v1 v2 v3 v4 v5
                                                v6
  = coe
      du_uv'8776'w'8658'xu'8729'v'8776'xw_106 (coe v0) (coe v1)
      (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v6)
      (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v6)
      (coe
         du_uv'8776'w'8658'u'8729'vx'8776'wx_112 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v6))
      (coe v5)
-- Algebra.Properties.Semigroup._.uv≈w⇒xy≈z⇒u[vx∙y]≈wz
d_uv'8776'w'8658'xy'8776'z'8658'u'91'vx'8729'y'93''8776'wz_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_uv'8776'w'8658'xy'8776'z'8658'u'91'vx'8729'y'93''8776'wz_192 ~v0
                                                               ~v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = du_uv'8776'w'8658'xy'8776'z'8658'u'91'vx'8729'y'93''8776'wz_192
      v2 v3 v4 v5 v6 v7 v8 v9 v10
du_uv'8776'w'8658'xy'8776'z'8658'u'91'vx'8729'y'93''8776'wz_192 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_uv'8776'w'8658'xy'8776'z'8658'u'91'vx'8729'y'93''8776'wz_192 v0
                                                                v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1)
         (\ v9 v10 -> v9)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v6) v7)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v5))
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v9 v10 -> v10)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v6) v7)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v5))
      (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v5)
      (coe
         MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
         (MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (MAlonzo.Code.Relation.Binary.Structures.d_refl_36
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)))))
         v1
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v6) v7)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v5)
         (coe
            du_uv'8776'w'8658'xu'8729'v'8776'xw_106 (coe v0) (coe v6) (coe v7)
            (coe v5) (coe v8) (coe v2)))
      (coe
         du_uv'8776'w'8658'u'8729'vx'8776'wx_112 (coe v0) (coe v1) (coe v2)
         (coe v3) (coe v4) (coe v5))
-- Algebra.Properties.Semigroup._.uv≈w⇒x∙wy≈x∙[u∙vy]
d_uv'8776'w'8658'x'8729'wy'8776'x'8729''91'u'8729'vy'93'_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_uv'8776'w'8658'x'8729'wy'8776'x'8729''91'u'8729'vy'93'_200 ~v0
                                                             ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_uv'8776'w'8658'x'8729'wy'8776'x'8729''91'u'8729'vy'93'_200
      v2 v3 v4 v5 v6 v7 v8
du_uv'8776'w'8658'x'8729'wy'8776'x'8729''91'u'8729'vy'93'_200 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_uv'8776'w'8658'x'8729'wy'8776'x'8729''91'u'8729'vy'93'_200 v0 v1
                                                              v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_38
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v6)))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v6))
      (coe
         du_uv'8776'w'8658'x'91'uv'8729'y'93''8776'x'8729'wy_130 (coe v0)
         (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) (coe v6))
-- Algebra.Properties.Semigroup._.[uv∙w]x≈u[vw∙x]
d_'91'uv'8729'w'93'x'8776'u'91'vw'8729'x'93'_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'91'uv'8729'w'93'x'8776'u'91'vw'8729'x'93'_214 ~v0 ~v1 v2 v3 v4
                                                 v5 v6
  = du_'91'uv'8729'w'93'x'8776'u'91'vw'8729'x'93'_214 v2 v3 v4 v5 v6
du_'91'uv'8729'w'93'x'8776'u'91'vw'8729'x'93'_214 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'91'uv'8729'w'93'x'8776'u'91'vw'8729'x'93'_214 v0 v1 v2 v3 v4
  = coe
      du_uv'8776'w'8658''91'xu'8729'v'93'y'8776'x'8729'wy_150 (coe v0)
      (coe v2) (coe v3)
      (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v3)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v3))
      (coe v1) (coe v4)
-- Algebra.Properties.Semigroup._.[uv∙w]x≈u[v∙wx]
d_'91'uv'8729'w'93'x'8776'u'91'v'8729'wx'93'_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'91'uv'8729'w'93'x'8776'u'91'v'8729'wx'93'_216 ~v0 ~v1 v2 v3 v4
                                                 v5 v6
  = du_'91'uv'8729'w'93'x'8776'u'91'v'8729'wx'93'_216 v2 v3 v4 v5 v6
du_'91'uv'8729'w'93'x'8776'u'91'v'8729'wx'93'_216 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'91'uv'8729'w'93'x'8776'u'91'v'8729'wx'93'_216 v0 v1 v2 v3 v4
  = coe
      du_uv'8776'w'8658''91'xy'8729'u'93'v'8776'x'8729'yw_160 (coe v0)
      (coe v3) (coe v4)
      (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v4)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v4))
      (coe v1) (coe v2)
-- Algebra.Properties.Semigroup._.[u∙vw]x≈uv∙wx
d_'91'u'8729'vw'93'x'8776'uv'8729'wx_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'91'u'8729'vw'93'x'8776'uv'8729'wx_218 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_'91'u'8729'vw'93'x'8776'uv'8729'wx_218 v2 v3 v4 v5 v6
du_'91'u'8729'vw'93'x'8776'uv'8729'wx_218 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'91'u'8729'vw'93'x'8776'uv'8729'wx_218 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v5 v6 -> v6)
         (\ v5 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v4)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v3)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v3)))
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (\ v5 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v4)
         (\ v5 v6 -> v5)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v3)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v3)))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v4))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (coe
            MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
            (\ v5 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v4)
            (\ v5 v6 -> v5)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v3)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v3)))
         (coe
            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
            (\ v5 v6 -> v6)
            (\ v5 -> coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v5 v4)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v3)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v3)))
         (coe
            MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
            (MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_496
                  (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
            (MAlonzo.Code.Relation.Binary.Structures.d_refl_36
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_496
                     (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)))))
            v4
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v3)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v3))
            (coe
               MAlonzo.Code.Algebra.Structures.d_assoc_498
               (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v1 v2
               v3)))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1 v2) v3 v4)
-- Algebra.Properties.Semigroup._.[u∙vw]x≈u[v∙wx]
d_'91'u'8729'vw'93'x'8776'u'91'v'8729'wx'93'_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'91'u'8729'vw'93'x'8776'u'91'v'8729'wx'93'_220 ~v0 ~v1 v2 v3 v4
                                                 v5 v6
  = du_'91'u'8729'vw'93'x'8776'u'91'v'8729'wx'93'_220 v2 v3 v4 v5 v6
du_'91'u'8729'vw'93'x'8776'u'91'v'8729'wx'93'_220 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'91'u'8729'vw'93'x'8776'u'91'v'8729'wx'93'_220 v0 v1 v2 v3 v4
  = coe
      du_uv'8776'w'8658''91'x'8729'yu'93'v'8776'x'8729'yw_140 (coe v0)
      (coe v3) (coe v4)
      (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v4)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v4))
      (coe v1) (coe v2)
-- Algebra.Properties.Semigroup._.uv∙wx≈u[vw∙x]
d_uv'8729'wx'8776'u'91'vw'8729'x'93'_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_uv'8729'wx'8776'u'91'vw'8729'x'93'_222 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_uv'8729'wx'8776'u'91'vw'8729'x'93'_222 v2 v3 v4 v5 v6
du_uv'8729'wx'8776'u'91'vw'8729'x'93'_222 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_uv'8729'wx'8776'u'91'vw'8729'x'93'_222 v0 v1 v2 v3 v4
  = coe
      du_uv'8776'w'8658'xu'8729'vy'8776'x'8729'wy_182 (coe v0) (coe v2)
      (coe v3) (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v3)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v3))
      (coe v1) (coe v4)
-- Algebra.Properties.Semigroup._.uv≈wx⇒yu∙v≈yw∙x
d_uv'8776'wx'8658'yu'8729'v'8776'yw'8729'x_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_uv'8776'wx'8658'yu'8729'v'8776'yw'8729'x_240 ~v0 ~v1 v2 v3 v4 v5
                                               v6 v7 v8
  = du_uv'8776'wx'8658'yu'8729'v'8776'yw'8729'x_240
      v2 v3 v4 v5 v6 v7 v8
du_uv'8776'wx'8658'yu'8729'v'8776'yw'8729'x_240 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_uv'8776'wx'8658'yu'8729'v'8776'yw'8729'x_240 v0 v1 v2 v3 v4 v5
                                                v6
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v1) v2)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v4))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v3) v4)
      (coe
         du_uv'8776'w'8658'xu'8729'v'8776'xw_106 (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v4) (coe v5)
         (coe v6))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v3) v4)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v4))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_498
            (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v6 v3
            v4))
-- Algebra.Properties.Semigroup._.uv≈wx⇒u∙vy≈w∙xy
d_uv'8776'wx'8658'u'8729'vy'8776'w'8729'xy_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_uv'8776'wx'8658'u'8729'vy'8776'w'8729'xy_246 ~v0 ~v1 v2 v3 v4 v5
                                               v6 v7 v8
  = du_uv'8776'wx'8658'u'8729'vy'8776'w'8729'xy_246
      v2 v3 v4 v5 v6 v7 v8
du_uv'8776'wx'8658'u'8729'vy'8776'w'8729'xy_246 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_uv'8776'wx'8658'u'8729'vy'8776'w'8729'xy_246 v0 v1 v2 v3 v4 v5
                                                v6
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v1
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v6))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v4) v6)
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v4 v6))
      (coe
         du_uv'8776'w'8658'u'8729'vx'8776'wx_112 (coe v0) (coe v1) (coe v2)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3 v4) (coe v5)
         (coe v6))
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_498
         (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v3 v4 v6)
-- Algebra.Properties.Semigroup._.uv≈wx⇒yu∙vz≈yw∙xz
d_uv'8776'wx'8658'yu'8729'vz'8776'yw'8729'xz_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_uv'8776'wx'8658'yu'8729'vz'8776'yw'8729'xz_254 ~v0 ~v1 v2 v3 v4
                                                 v5 v6 v7 v8 v9
  = du_uv'8776'wx'8658'yu'8729'vz'8776'yw'8729'xz_254
      v2 v3 v4 v5 v6 v7 v8 v9
du_uv'8776'wx'8658'yu'8729'vz'8776'yw'8729'xz_254 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_558 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_uv'8776'wx'8658'yu'8729'vz'8776'yw'8729'xz_254 v0 v1 v2 v3 v4 v5
                                                  v6 v7
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
      (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_496
            (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v1)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v7))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v4 v7)))
      (coe
         MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v3)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v4 v7))
      (coe
         du_uv'8776'w'8658'xu'8729'v'8776'xw_106 (coe v0) (coe v1)
         (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v2 v7)
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v4 v7))
         (coe
            du_uv'8776'wx'8658'u'8729'vy'8776'w'8729'xy_246 (coe v0) (coe v1)
            (coe v2) (coe v3) (coe v4) (coe v5) (coe v7))
         (coe v6))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_496
               (coe MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0))))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6 v3)
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v4 v7))
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v6
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v3
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v4 v7)))
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_498
            (MAlonzo.Code.Algebra.Bundles.d_isSemigroup_578 (coe v0)) v6 v3
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__576 v0 v4 v7)))
