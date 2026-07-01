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

module MAlonzo.Code.Algebra.Construct.LiftedChoice where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Consequences.Base
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Construct.LiftedChoice._.Lift
d_Lift_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_Lift_30 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_Lift_30 v7 v8 v9 v10
du_Lift_30 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_Lift_30 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66 (\ v4 -> v2)
      (\ v4 -> v3) (coe v0 (coe v1 v2) (coe v1 v3))
-- Algebra.Construct.LiftedChoice._._._◦_
d__'9702'__128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d__'9702'__128 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8
  = du__'9702'__128 v5 v8
du__'9702'__128 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'9702'__128 v0 v1
  = coe
      du_Lift_30 (coe MAlonzo.Code.Algebra.Structures.d_sel_460 (coe v0))
      (coe v1)
-- Algebra.Construct.LiftedChoice._._.sel-≡
d_sel'45''8801'_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel'45''8801'_130 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 v9 v10
  = du_sel'45''8801'_130 v5 v8 v9 v10
du_sel'45''8801'_130 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sel'45''8801'_130 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Algebra.Structures.d_sel_460 v0 (coe v1 v2)
      (coe v1 v3)
-- Algebra.Construct.LiftedChoice._._.distrib
d_distrib_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib_152 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 v9 v10
  = du_distrib_152 v5 v8 v9 v10
du_distrib_152 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib_152 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Algebra.Structures.d_sel_460 v0 (coe v1 v2)
              (coe v1 v3) in
    coe
      (case coe v4 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5 -> coe v5
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5 -> coe v5
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.LiftedChoice._._._◦_
d__'9702'__186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'9702'__186 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10
  = du__'9702'__186 v5 v8
du__'9702'__186 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'9702'__186 v0 v1
  = coe
      du_Lift_30 (coe MAlonzo.Code.Algebra.Structures.d_sel_460 (coe v0))
      (coe v1)
-- Algebra.Construct.LiftedChoice._._.sel
d_sel_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sel_188 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 v10 v11 v12
  = du_sel_188 v5 v8 v10 v11 v12
du_sel_188 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sel_188 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Sum.Base.du_map_84
      (coe v2 (coe du__'9702'__186 v0 v1 v3 v4) v3)
      (coe v2 (coe du__'9702'__186 v0 v1 v3 v4) v4)
      (coe du_sel'45''8801'_130 (coe v0) (coe v1) (coe v3) (coe v4))
-- Algebra.Construct.LiftedChoice._._.idem
d_idem_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny -> AgdaAny
d_idem_194 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 v10
  = du_idem_194 v5 v8 v10
du_idem_194 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny -> AgdaAny
du_idem_194 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Consequences.Base.du_sel'8658'idem_80
      (coe du_sel_188 (coe v0) (coe v1) (coe v2))
-- Algebra.Construct.LiftedChoice._._._◦_
d__'9702'__212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'9702'__212 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 v8 ~v9 ~v10
  = du__'9702'__212 v5 v8
du__'9702'__212 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'9702'__212 v0 v1
  = coe
      du_Lift_30 (coe MAlonzo.Code.Algebra.Structures.d_sel_460 (coe v0))
      (coe v1)
-- Algebra.Construct.LiftedChoice._._.cong
d_cong_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_cong_214 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 v8 ~v9 v10 v11 v12 v13 v14
           v15 v16 v17
  = du_cong_214 v4 v5 v8 v10 v11 v12 v13 v14 v15 v16 v17
du_cong_214 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_cong_214 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = let v11
          = coe
              MAlonzo.Code.Algebra.Structures.d_sel_460 v1 (coe v2 v5)
              (coe v2 v7) in
    coe
      (let v12
             = coe
                 MAlonzo.Code.Algebra.Structures.d_sel_460 v1 (coe v2 v6)
                 (coe v2 v8) in
       coe
         (case coe v11 of
            MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
              -> case coe v12 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14 -> coe v9
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14
                     -> coe
                          v3 v5 v8
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                             (\ v15 v16 v17 ->
                                coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36
                                  v17)
                             (coe v2 v5) (coe v2 v8)
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isMagma_458
                                            (coe v1)))))
                                (coe v2 v5) (coe v0 (coe v2 v5) (coe v2 v7)) (coe v2 v8)
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMagma_458
                                               (coe v1)))))
                                   (coe v0 (coe v2 v5) (coe v2 v7)) (coe v0 (coe v2 v6) (coe v2 v8))
                                   (coe v2 v8)
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isMagma_458
                                                  (coe v1)))))
                                      (coe v0 (coe v2 v6) (coe v2 v8)) (coe v2 v8) (coe v2 v8)
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isMagma_458
                                                     (coe v1)))))
                                         (coe v2 v8))
                                      v14)
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
                                      (MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1))
                                      (coe v2 v5) (coe v2 v6) (coe v2 v7) (coe v2 v8)
                                      (coe v4 v5 v6 v9) (coe v4 v7 v8 v10)))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                                   (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                                      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1)))
                                   (coe v0 (coe v2 v5) (coe v2 v7)) (coe v2 v5) v13)))
                   _ -> MAlonzo.RTE.mazUnreachableError
            MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
              -> case coe v12 of
                   MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v14
                     -> coe
                          v3 v7 v6
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                             (\ v15 v16 v17 ->
                                coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36
                                  v17)
                             (coe v2 v7) (coe v2 v6)
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                      (coe
                                         MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isMagma_458
                                            (coe v1)))))
                                (coe v2 v7) (coe v0 (coe v2 v5) (coe v2 v7)) (coe v2 v6)
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                         (coe
                                            MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isMagma_458
                                               (coe v1)))))
                                   (coe v0 (coe v2 v5) (coe v2 v7)) (coe v0 (coe v2 v6) (coe v2 v8))
                                   (coe v2 v6)
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                                            (coe
                                               MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isMagma_458
                                                  (coe v1)))))
                                      (coe v0 (coe v2 v6) (coe v2 v8)) (coe v2 v6) (coe v2 v6)
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                                                  (coe
                                                     MAlonzo.Code.Algebra.Structures.d_isMagma_458
                                                     (coe v1)))))
                                         (coe v2 v6))
                                      v14)
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
                                      (MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1))
                                      (coe v2 v5) (coe v2 v6) (coe v2 v7) (coe v2 v8)
                                      (coe v4 v5 v6 v9) (coe v4 v7 v8 v10)))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                                   (MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                                      (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1)))
                                   (coe v0 (coe v2 v5) (coe v2 v7)) (coe v2 v7) v13)))
                   MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v14 -> coe v10
                   _ -> MAlonzo.RTE.mazUnreachableError
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Algebra.Construct.LiftedChoice._._.assoc
d_assoc_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_306 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 v8 ~v9 v10 v11 v12 v13
            v14
  = du_assoc_306 v4 v5 v8 v10 v11 v12 v13 v14
du_assoc_306 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_306 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      v3 (coe du__'9702'__212 v1 v2 (coe du__'9702'__212 v1 v2 v5 v6) v7)
      (coe du__'9702'__212 v1 v2 v5 (coe du__'9702'__212 v1 v2 v6 v7))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v8 v9 v10 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v10)
         (coe
            v2
            (coe du__'9702'__212 v1 v2 (coe du__'9702'__212 v1 v2 v5 v6) v7))
         (coe
            v2
            (coe du__'9702'__212 v1 v2 v5 (coe du__'9702'__212 v1 v2 v6 v7)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1)))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1))))
            (coe
               v2
               (coe du__'9702'__212 v1 v2 (coe du__'9702'__212 v1 v2 v5 v6) v7))
            (coe v0 (coe v2 (coe du__'9702'__212 v1 v2 v5 v6)) (coe v2 v7))
            (coe
               v2
               (coe du__'9702'__212 v1 v2 v5 (coe du__'9702'__212 v1 v2 v6 v7)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1)))))
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1))))
               (coe v0 (coe v2 (coe du__'9702'__212 v1 v2 v5 v6)) (coe v2 v7))
               (coe v0 (coe v0 (coe v2 v5) (coe v2 v6)) (coe v2 v7))
               (coe
                  v2
                  (coe du__'9702'__212 v1 v2 v5 (coe du__'9702'__212 v1 v2 v6 v7)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1)))))
                  (coe v0 (coe v0 (coe v2 v5) (coe v2 v6)) (coe v2 v7))
                  (coe v0 (coe v2 v5) (coe v0 (coe v2 v6) (coe v2 v7)))
                  (coe
                     v2
                     (coe du__'9702'__212 v1 v2 v5 (coe du__'9702'__212 v1 v2 v6 v7)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1)))))
                     (coe v0 (coe v2 v5) (coe v0 (coe v2 v6) (coe v2 v7)))
                     (coe v0 (coe v2 v5) (coe v2 (coe du__'9702'__212 v1 v2 v6 v7)))
                     (coe
                        v2
                        (coe du__'9702'__212 v1 v2 v5 (coe du__'9702'__212 v1 v2 v6 v7)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1)))))
                        (coe v0 (coe v2 v5) (coe v2 (coe du__'9702'__212 v1 v2 v6 v7)))
                        (coe
                           v2
                           (coe du__'9702'__212 v1 v2 v5 (coe du__'9702'__212 v1 v2 v6 v7)))
                        (coe
                           v2
                           (coe du__'9702'__212 v1 v2 v5 (coe du__'9702'__212 v1 v2 v6 v7)))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                                    (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1)))))
                           (coe
                              v2
                              (coe du__'9702'__212 v1 v2 v5 (coe du__'9702'__212 v1 v2 v6 v7))))
                        (coe
                           du_distrib_152 (coe v1) (coe v2) (coe v5)
                           (coe du__'9702'__212 v1 v2 v6 v7)))
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1)))
                        (MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1))))
                        (coe v2 v5) (coe v0 (coe v2 v6) (coe v2 v7))
                        (coe v2 (coe du__'9702'__128 v1 v2 v6 v7))
                        (coe du_distrib_152 (coe v1) (coe v2) (coe v6) (coe v7))))
                  (coe v4 (coe v2 v5) (coe v2 v6) (coe v2 v7)))
               (coe
                  MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                  (MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_188
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1)))
                  (MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1))))
                  (coe v2 v7) (coe v0 (coe v2 v5) (coe v2 v6))
                  (coe v2 (coe du__'9702'__128 v1 v2 v5 v6))
                  (coe du_distrib_152 (coe v1) (coe v2) (coe v5) (coe v6))))
            (coe
               du_distrib_152 (coe v1) (coe v2) (coe du__'9702'__212 v1 v2 v5 v6)
               (coe v7))))
-- Algebra.Construct.LiftedChoice._._.comm
d_comm_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_316 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 v8 ~v9 v10 v11 v12 v13
  = du_comm_316 v4 v5 v8 v10 v11 v12 v13
du_comm_316 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_316 v0 v1 v2 v3 v4 v5 v6
  = coe
      v3 (coe du__'9702'__212 v1 v2 v5 v6)
      (coe du__'9702'__212 v1 v2 v6 v5)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v9)
         (coe v2 (coe du__'9702'__212 v1 v2 v5 v6))
         (coe v2 (coe du__'9702'__212 v1 v2 v6 v5))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_372
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                     (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1)))))
            (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                  (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1))))
            (coe v2 (coe du__'9702'__212 v1 v2 v5 v6))
            (coe v0 (coe v2 v5) (coe v2 v6))
            (coe v2 (coe du__'9702'__212 v1 v2 v6 v5))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1)))))
               (coe v0 (coe v2 v5) (coe v2 v6)) (coe v0 (coe v2 v6) (coe v2 v5))
               (coe v2 (coe du__'9702'__212 v1 v2 v6 v5))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_40
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1)))))
                  (coe v0 (coe v2 v6) (coe v2 v5))
                  (coe v2 (coe du__'9702'__212 v1 v2 v6 v5))
                  (coe v2 (coe du__'9702'__212 v1 v2 v6 v5))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_36
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_186
                              (coe MAlonzo.Code.Algebra.Structures.d_isMagma_458 (coe v1)))))
                     (coe v2 (coe du__'9702'__212 v1 v2 v6 v5)))
                  (coe du_distrib_152 (coe v1) (coe v2) (coe v6) (coe v5)))
               (coe v4 (coe v2 v5) (coe v2 v6)))
            (coe du_distrib_152 (coe v1) (coe v2) (coe v5) (coe v6))))
-- Algebra.Construct.LiftedChoice._._._◦_
d__'9702'__356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'9702'__356 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11 ~v12
  = du__'9702'__356 v5 v9
du__'9702'__356 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'9702'__356 v0 v1
  = coe
      du_Lift_30 (coe MAlonzo.Code.Algebra.Structures.d_sel_460 (coe v0))
      (coe v1)
-- Algebra.Construct.LiftedChoice._._.isMagma
d_isMagma_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
d_isMagma_358 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 v9 v10 v11 v12
  = du_isMagma_358 v4 v5 v9 v10 v11 v12
du_isMagma_358 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_178
du_isMagma_358 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_210 (coe v5)
      (coe du_cong_214 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Algebra.Construct.LiftedChoice._._.isSemigroup
d_isSemigroup_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
d_isSemigroup_362 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 v9 v10 v11 v12
                  v13
  = du_isSemigroup_362 v4 v5 v9 v10 v11 v12 v13
du_isSemigroup_362 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_488
du_isSemigroup_362 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_522
      (coe
         du_isMagma_358 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
      (coe du_assoc_306 (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))
-- Algebra.Construct.LiftedChoice._._.isBand
d_isBand_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
d_isBand_368 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 v9 v10 v11 v12 v13
  = du_isBand_368 v4 v5 v9 v10 v11 v12 v13
du_isBand_368 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsBand_526
du_isBand_368 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_564
      (coe
         du_isSemigroup_362 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5) (coe v6))
      (coe
         du_idem_194 (coe v1) (coe v2)
         (\ v7 v8 v9 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42 (coe v5)
              v7))
-- Algebra.Construct.LiftedChoice._._.isSelectiveMagma
d_isSelectiveMagma_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450
d_isSelectiveMagma_372 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 v9 v10 v11
                       v12
  = du_isSelectiveMagma_372 v4 v5 v9 v10 v11 v12
du_isSelectiveMagma_372 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450
du_isSelectiveMagma_372 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.C_constructor_484
      (coe
         du_isMagma_358 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
      (coe
         du_sel_188 (coe v1) (coe v2)
         (\ v6 v7 v8 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42 (coe v5)
              v6))
-- Algebra.Construct.LiftedChoice._._._◦_
d__'9702'__386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d__'9702'__386 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10
  = du__'9702'__386 v5 v10
du__'9702'__386 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'9702'__386 v0 v1
  = coe
      du_Lift_30 (coe MAlonzo.Code.Algebra.Structures.d_sel_460 (coe v0))
      (coe v1)
-- Algebra.Construct.LiftedChoice._._.preservesᵒ
d_preserves'7506'_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
d_preserves'7506'_400 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10
                      v11 v12 v13 v14 v15
  = du_preserves'7506'_400 v5 v10 v11 v12 v13 v14 v15
du_preserves'7506'_400 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> AgdaAny
du_preserves'7506'_400 v0 v1 v2 v3 v4 v5 v6
  = case coe v6 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
        -> let v8
                 = coe
                     MAlonzo.Code.Algebra.Structures.d_sel_460 v0 (coe v1 v4)
                     (coe v1 v5) in
           coe
             (case coe v8 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> coe v7
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9 -> coe v2 v4 v5 v7 v9
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
        -> let v8
                 = coe
                     MAlonzo.Code.Algebra.Structures.d_sel_460 v0 (coe v1 v4)
                     (coe v1 v5) in
           coe
             (case coe v8 of
                MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9 -> coe v3 v4 v5 v7 v9
                MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9 -> coe v7
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Construct.LiftedChoice._._.preservesʳ
d_preserves'691'_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_preserves'691'_482 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                     v12 v13 v14
  = du_preserves'691'_482 v5 v10 v11 v12 v13 v14
du_preserves'691'_482 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_preserves'691'_482 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Algebra.Structures.d_sel_460 v0 (coe v1 v3)
              (coe v1 v4) in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> coe v2 v3 v4 v5 v7
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7 -> coe v5
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.LiftedChoice._._.preservesᵇ
d_preserves'7495'_520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_preserves'7495'_520 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10
                      v11 v12 v13 v14
  = du_preserves'7495'_520 v5 v10 v11 v12 v13 v14
du_preserves'7495'_520 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_preserves'7495'_520 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Algebra.Structures.d_sel_460 v0 (coe v1 v2)
              (coe v1 v3) in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7 -> coe v4
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7 -> coe v5
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Algebra.Construct.LiftedChoice._._.forcesᵇ
d_forces'7495'_562 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_forces'7495'_562 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                   v12 v13 v14 v15
  = du_forces'7495'_562 v5 v10 v11 v12 v13 v14 v15
du_forces'7495'_562 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_450 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_forces'7495'_562 v0 v1 v2 v3 v4 v5 v6
  = let v7
          = coe
              MAlonzo.Code.Algebra.Structures.d_sel_460 v0 (coe v1 v4)
              (coe v1 v5) in
    coe
      (case coe v7 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v8
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                (coe
                   v2
                   (coe
                      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52 (coe (\ v9 -> v4))
                      (coe (\ v9 -> v5)) (coe v7))
                   v5 v6 v8)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v8
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   v3 v4
                   (coe
                      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52 (coe (\ v9 -> v4))
                      (coe (\ v9 -> v5)) (coe v7))
                   v6 v8)
                (coe v6)
         _ -> MAlonzo.RTE.mazUnreachableError)
