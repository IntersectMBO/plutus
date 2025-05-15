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

module MAlonzo.Code.Algebra.Properties.QQuasigroup where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Base.Single qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Syntax qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Properties.Quasigroup._.Cancellative
d_Cancellative_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Cancellative_112 = erased
-- Algebra.Properties.Quasigroup._.LeftCancellative
d_LeftCancellative_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftCancellative_144 = erased
-- Algebra.Properties.Quasigroup._.RightCancellative
d_RightCancellative_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightCancellative_174 = erased
-- Algebra.Properties.Quasigroup.cancelˡ
d_cancel'737'_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'737'_256 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_cancel'737'_256 v2 v3 v4 v5 v6
du_cancel'737'_256 ::
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'737'_256 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      v2 v3
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v5
                      = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5))))))
         v2
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'92''92'__4270 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v1 v2))
         v3
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5)))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'92''92'__4270 v0 v1
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v1 v2))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'92''92'__4270 v0 v1
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v1 v3))
            v3
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v5
                               = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5)))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'92''92'__4270 v0 v1
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v1 v3))
               v3 v3
               (let v5
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v5
                                    = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v5))
                     (coe v3)))
               (coe
                  MAlonzo.Code.Algebra.Structures.du_leftDivides'691'_3012
                  (MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0)) v1 v3))
            (coe
               MAlonzo.Code.Algebra.Structures.du_'92''92''45'cong'737'_2994
               (coe MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0))
               (coe v1)
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v1 v2)
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v1 v3)
               (coe v4)))
         (coe
            MAlonzo.Code.Algebra.Structures.du_leftDivides'691'_3012
            (MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0)) v1 v2))
-- Algebra.Properties.Quasigroup.cancelʳ
d_cancel'691'_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cancel'691'_266 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_cancel'691'_266 v2 v3 v4 v5 v6
du_cancel'691'_266 ::
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cancel'691'_266 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      v2 v3
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v5
                      = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5))))))
         v2
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'47''47'__4272 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v2 v1) v1)
         v3
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5)))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'47''47'__4272 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v2 v1) v1)
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'47''47'__4272 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v3 v1) v1)
            v3
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (let v5
                               = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5)))))))
               (coe
                  MAlonzo.Code.Algebra.Bundles.d__'47''47'__4272 v0
                  (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v3 v1) v1)
               v3 v3
               (let v5
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (let v5
                                    = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                              coe
                                (coe
                                   MAlonzo.Code.Algebra.Structures.du_setoid_200
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5))))) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v5))
                     (coe v3)))
               (coe
                  MAlonzo.Code.Algebra.Structures.du_rightDivides'691'_3016
                  (MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0)) v1 v3))
            (coe
               MAlonzo.Code.Algebra.Structures.du_'47''47''45'cong'691'_3006
               (coe MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0))
               (coe v1)
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v2 v1)
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v3 v1)
               (coe v4)))
         (coe
            MAlonzo.Code.Algebra.Structures.du_rightDivides'691'_3016
            (MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0)) v1 v2))
-- Algebra.Properties.Quasigroup.cancel
d_cancel_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cancel_276 ~v0 ~v1 v2 = du_cancel_276 v2
du_cancel_276 ::
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cancel_276 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_cancel'737'_256 (coe v0)) (coe du_cancel'691'_266 (coe v0))
-- Algebra.Properties.Quasigroup.y≈x\\z
d_y'8776'x'92''92'z_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_y'8776'x'92''92'z_284 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_y'8776'x'92''92'z_284 v2 v3 v4 v5 v6
du_y'8776'x'92''92'z_284 ::
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_y'8776'x'92''92'z_284 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      v2 (coe MAlonzo.Code.Algebra.Bundles.d__'92''92'__4270 v0 v1 v3)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v5
                      = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5))))))
         v2
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'92''92'__4270 v0 v1
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v1 v2))
         (coe MAlonzo.Code.Algebra.Bundles.d__'92''92'__4270 v0 v1 v3)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5)))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'92''92'__4270 v0 v1
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v1 v2))
            (coe MAlonzo.Code.Algebra.Bundles.d__'92''92'__4270 v0 v1 v3)
            (coe MAlonzo.Code.Algebra.Bundles.d__'92''92'__4270 v0 v1 v3)
            (let v5
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v5
                                 = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                           coe
                             (coe
                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v5))
                  (coe MAlonzo.Code.Algebra.Bundles.d__'92''92'__4270 v0 v1 v3)))
            (coe
               MAlonzo.Code.Algebra.Structures.du_'92''92''45'cong'737'_2994
               (coe MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0))
               (coe v1)
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v1 v2)
               (coe v3) (coe v4)))
         (coe
            MAlonzo.Code.Algebra.Structures.du_leftDivides'691'_3012
            (MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0)) v1 v2))
-- Algebra.Properties.Quasigroup.x≈z//y
d_x'8776'z'47''47'y_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_x'8776'z'47''47'y_300 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_x'8776'z'47''47'y_300 v2 v3 v4 v5 v6
du_x'8776'z'47''47'y_300 ::
  MAlonzo.Code.Algebra.Bundles.T_Quasigroup_4246 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_x'8776'z'47''47'y_300 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v5 v6 v7 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
      v1 (coe MAlonzo.Code.Algebra.Bundles.d__'47''47'__4272 v0 v3 v2)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (let v5
                         = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5)))))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
               (let v5
                      = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_setoid_200
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5))))))
         v1
         (coe
            MAlonzo.Code.Algebra.Bundles.d__'47''47'__4272 v0
            (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v1 v2) v2)
         (coe MAlonzo.Code.Algebra.Bundles.d__'47''47'__4272 v0 v3 v2)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (let v5
                            = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5)))))))
            (coe
               MAlonzo.Code.Algebra.Bundles.d__'47''47'__4272 v0
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v1 v2) v2)
            (coe MAlonzo.Code.Algebra.Bundles.d__'47''47'__4272 v0 v3 v2)
            (coe MAlonzo.Code.Algebra.Bundles.d__'47''47'__4272 v0 v3 v2)
            (let v5
                   = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                          (let v5
                                 = MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0) in
                           coe
                             (coe
                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                (coe MAlonzo.Code.Algebra.Structures.d_isMagma_2962 (coe v5))))) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (coe v5))
                  (coe MAlonzo.Code.Algebra.Bundles.d__'47''47'__4272 v0 v3 v2)))
            (coe
               MAlonzo.Code.Algebra.Structures.du_'47''47''45'cong'691'_3006
               (coe MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0))
               (coe v2)
               (coe MAlonzo.Code.Algebra.Bundles.d__'8729'__4268 v0 v1 v2)
               (coe v3) (coe v4)))
         (coe
            MAlonzo.Code.Algebra.Structures.du_rightDivides'691'_3016
            (MAlonzo.Code.Algebra.Bundles.d_isQuasigroup_4274 (coe v0)) v2 v1))
