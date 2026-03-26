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

module MAlonzo.Code.VerifiedCompilation.UCaseReduce.Equivalence where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.CEK
import qualified MAlonzo.Code.Untyped.Equality
import qualified MAlonzo.Code.Untyped.Reduction
import qualified MAlonzo.Code.Untyped.Relation
import qualified MAlonzo.Code.Untyped.Transform
import qualified MAlonzo.Code.VerifiedCompilation.Certificate
import qualified MAlonzo.Code.VerifiedCompilation.Trace
import qualified MAlonzo.Code.VerifiedCompilation.UCaseReduce.Inductive
import qualified MAlonzo.Code.VerifiedCompilation.UntypedTranslation
import qualified MAlonzo.Code.VerifiedCompilation.UntypedViews

-- VerifiedCompilation.UCaseReduce.Equivalence.reduce
d_reduce_30 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_reduce_30 ~v0 v1 = du_reduce_30 v1
du_reduce_30 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
du_reduce_30 v0
  = case coe v0 of
      MAlonzo.Code.Untyped.C_case_40 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Untyped.C_constr_34 v3 v4
               -> let v5
                        = coe
                            MAlonzo.Code.Untyped.CEK.du_lookup'63'_996 (coe v3) (coe v2) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                         -> coe
                              MAlonzo.Code.Untyped.Reduction.du_iterApp_242 (coe v6) (coe v4)
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v0
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe v0
      _ -> coe v0
-- VerifiedCompilation.UCaseReduce.Equivalence.norm
d_norm_48 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_norm_48 v0 v1
  = coe
      MAlonzo.Code.Untyped.Transform.d__'8593'__8
      (\ v2 v3 -> coe du_reduce_30 v3) (coe v0) (coe v1)
-- VerifiedCompilation.UCaseReduce.Equivalence.norm*
d_norm'42'_54 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d_norm'42'_54 v0 v1
  = coe
      MAlonzo.Code.Untyped.Transform.d__'8593''42'__14
      (\ v2 v3 -> coe du_reduce_30 v3) (coe v0) (coe v1)
-- VerifiedCompilation.UCaseReduce.Equivalence.CaseReduce
d_CaseReduce_58 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_CaseReduce_58 = erased
-- VerifiedCompilation.UCaseReduce.Equivalence.decide
d_decide_70 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.Certificate.T_ProofOrCE_38
d_decide_70 v0 v1 v2
  = let v3
          = MAlonzo.Code.Untyped.Equality.d_decEq'45''8866'_56
              (coe v0)
              (coe
                 du_reduce_30
                 (coe
                    MAlonzo.Code.Untyped.Transform.du_'46'extendedlambda0_38
                    (\ v3 v4 -> coe du_reduce_30 v4) (coe v0) (coe v1)))
              (coe d_norm_48 (coe v0) (coe v2)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then case coe v5 of
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v6
                         -> coe
                              MAlonzo.Code.VerifiedCompilation.Certificate.C_proof_44 (coe v6)
                       _ -> MAlonzo.RTE.mazUnreachableError
                else coe
                       seq (coe v5)
                       (coe
                          MAlonzo.Code.VerifiedCompilation.Certificate.C_ce_52
                          (coe MAlonzo.Code.VerifiedCompilation.Trace.C_caseReduceT_14) v1
                          v2)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- VerifiedCompilation.UCaseReduce.Equivalence._~_
d__'126'__94 a0 a1 a2 = ()
data T__'126'__94
  = C_case'45'constr_100 MAlonzo.Code.Untyped.T__'8866'_14 |
    C_'126''45'refl_102 |
    C_'126''45'trans_104 MAlonzo.Code.Untyped.T__'8866'_14 T__'126'__94
                         T__'126'__94 |
    C_'126''45'sym_106 T__'126'__94 | C_'126''45'var_110 |
    C_'126''45'lam_112 T__'126'__94 |
    C_'126''45'app_114 T__'126'__94 T__'126'__94 |
    C_'126''45'force_116 T__'126'__94 |
    C_'126''45'delay_118 T__'126'__94 |
    C_'126''45'constr_120 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 |
    C_'126''45'case_122 T__'126'__94
                        MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 |
    C_'126''45'con_126 | C_'126''45'builtin_130 | C_'126''45'error_132
-- VerifiedCompilation.UCaseReduce.Equivalence.~-compat
d_'126''45'compat_134 ::
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_118
d_'126''45'compat_134
  = coe
      MAlonzo.Code.Untyped.Relation.C_constructor_238
      (coe (\ v0 v1 -> coe C_'126''45'var_110))
      (coe (\ v0 v1 v2 v3 -> coe C_'126''45'lam_112 v3))
      (coe (\ v0 v1 v2 v3 v4 v5 v6 -> coe C_'126''45'app_114 v5 v6))
      (coe (\ v0 v1 v2 v3 -> coe C_'126''45'force_116 v3))
      (coe (\ v0 v1 v2 v3 -> coe C_'126''45'delay_118 v3))
      (coe (\ v0 v1 v2 v3 -> coe C_'126''45'constr_120))
      (coe (\ v0 v1 v2 v3 v4 v5 v6 -> coe C_'126''45'case_122 v5 v6))
      (coe (\ v0 v1 -> coe C_'126''45'con_126))
      (coe (\ v0 v1 -> coe C_'126''45'builtin_130))
      (coe (\ v0 -> coe C_'126''45'error_132))
-- VerifiedCompilation.UCaseReduce.Equivalence.~-setoid
d_'126''45'setoid_136 ::
  Integer -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'126''45'setoid_136 ~v0 = du_'126''45'setoid_136
du_'126''45'setoid_136 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_'126''45'setoid_136
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_46
         (\ v0 -> coe C_'126''45'refl_102)
         (\ v0 v1 v2 -> coe C_'126''45'sym_106 v2)
         (\ v0 v1 v2 v3 v4 -> coe C_'126''45'trans_104 v1 v3 v4))
-- VerifiedCompilation.UCaseReduce.Equivalence.reduce-id
d_reduce'45'id_144 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_case'7510'_926 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduce'45'id_144 = erased
-- VerifiedCompilation.UCaseReduce.Equivalence.reduce-~
d_reduce'45''126'_282 ::
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> T__'126'__94
d_reduce'45''126'_282 ~v0 v1 = du_reduce'45''126'_282 v1
du_reduce'45''126'_282 ::
  MAlonzo.Code.Untyped.T__'8866'_14 -> T__'126'__94
du_reduce'45''126'_282 v0
  = let v1
          = coe
              MAlonzo.Code.VerifiedCompilation.UntypedViews.du_constr'63'_1618
              (\ v1 ->
                 coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158)
              (\ v1 ->
                 coe
                   MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158) in
    coe
      (let v2
             = \ v2 ->
                 coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
       coe
         (case coe v0 of
            MAlonzo.Code.Untyped.C_'96'_18 v3 -> coe C_'126''45'refl_102
            MAlonzo.Code.Untyped.C_ƛ_20 v3 -> coe C_'126''45'refl_102
            MAlonzo.Code.Untyped.C__'183'__22 v3 v4 -> coe C_'126''45'refl_102
            MAlonzo.Code.Untyped.C_force_24 v3 -> coe C_'126''45'refl_102
            MAlonzo.Code.Untyped.C_delay_26 v3 -> coe C_'126''45'refl_102
            MAlonzo.Code.Untyped.C_con_28 v3 -> coe C_'126''45'refl_102
            MAlonzo.Code.Untyped.C_constr_34 v3 v4 -> coe C_'126''45'refl_102
            MAlonzo.Code.Untyped.C_case_40 v3 v4
              -> let v5
                       = coe
                           MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                           (coe v1 v3) (coe v2 v4) in
                 coe
                   (case coe v5 of
                      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                        -> if coe v6
                             then case coe v7 of
                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v8
                                      -> case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                             -> case coe v9 of
                                                  MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v13 v14
                                                    -> case coe v3 of
                                                         MAlonzo.Code.Untyped.C_constr_34 v15 v16
                                                           -> coe
                                                                seq (coe v13)
                                                                (coe
                                                                   seq (coe v14)
                                                                   (coe
                                                                      seq (coe v10)
                                                                      (let v17
                                                                             = coe
                                                                                 MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                                 (coe v15)
                                                                                 (coe v4) in
                                                                       coe
                                                                         (case coe v17 of
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                              -> coe
                                                                                   C_case'45'constr_100
                                                                                   v18
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                              -> coe
                                                                                   C_'126''45'refl_102
                                                                            _ -> MAlonzo.RTE.mazUnreachableError))))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             else (let v8
                                         = seq
                                             (coe v7)
                                             (coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                (coe v6)
                                                (coe
                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                   coe
                                     (case coe v8 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                          -> if coe v9
                                               then case coe v10 of
                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v11
                                                        -> case coe v11 of
                                                             MAlonzo.Code.VerifiedCompilation.UntypedViews.C_case'33'_936 v14 v15
                                                               -> case coe v14 of
                                                                    MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v18 v19
                                                                      -> case coe v3 of
                                                                           MAlonzo.Code.Untyped.C_constr_34 v20 v21
                                                                             -> coe
                                                                                  seq (coe v18)
                                                                                  (coe
                                                                                     seq (coe v19)
                                                                                     (coe
                                                                                        seq
                                                                                        (coe v15)
                                                                                        (let v22
                                                                                               = coe
                                                                                                   MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                                                   (coe
                                                                                                      v20)
                                                                                                   (coe
                                                                                                      v4) in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v22 of
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v23
                                                                                                -> coe
                                                                                                     C_case'45'constr_100
                                                                                                     v23
                                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                -> coe
                                                                                                     C_'126''45'refl_102
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError))))
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               else coe seq (coe v10) (coe C_'126''45'refl_102)
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                      _ -> MAlonzo.RTE.mazUnreachableError)
            MAlonzo.Code.Untyped.C_builtin_44 v3 -> coe C_'126''45'refl_102
            MAlonzo.Code.Untyped.C_error_46 -> coe C_'126''45'refl_102
            _ -> MAlonzo.RTE.mazUnreachableError))
-- VerifiedCompilation.UCaseReduce.Equivalence.norm-∼
d_norm'45''8764'_330 ::
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> T__'126'__94
d_norm'45''8764'_330 v0 v1
  = coe
      MAlonzo.Code.Untyped.Transform.du_'8593''45'extensive_162
      (coe (\ v2 v3 v4 v5 v6 v7 -> coe C_'126''45'trans_104 v4 v6 v7))
      (coe d_'126''45'compat_134) (\ v2 v3 -> coe du_reduce_30 v3)
      (\ v2 v3 -> coe du_reduce'45''126'_282 v3) (coe v0) (coe v1)
-- VerifiedCompilation.UCaseReduce.Equivalence.sound
d_sound_350 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> T__'126'__94
d_sound_350 v0 v1 v2 ~v3 = du_sound_350 v0 v1 v2
du_sound_350 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 -> T__'126'__94
du_sound_350 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v3 v4 v5 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
      v1 v2
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (\ v3 v4 v5 v6 v7 -> coe C_'126''45'trans_104 v4 v6 v7))
         v1 (d_norm_48 (coe v0) (coe v1)) v2
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_438
            (\ v3 v4 v5 v6 v7 -> v7) (d_norm_48 (coe v0) (coe v1))
            (d_norm_48 (coe v0) (coe v2)) v2
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_370
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (\ v3 v4 v5 v6 v7 -> coe C_'126''45'trans_104 v4 v6 v7))
               (d_norm_48 (coe v0) (coe v2)) v2 v2
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_494
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                     (\ v3 -> coe C_'126''45'refl_102))
                  (coe v2))
               (coe C_'126''45'sym_106 (d_norm'45''8764'_330 (coe v0) (coe v2))))
            erased)
         (d_norm'45''8764'_330 (coe v0) (coe v1)))
-- VerifiedCompilation.UCaseReduce.Equivalence.iterApp-norm
d_iterApp'45'norm_408 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_iterApp'45'norm_408 = erased
-- VerifiedCompilation.UCaseReduce.Equivalence.iterApp-≡
d_iterApp'45''8801'_412 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_iterApp'45''8801'_412 = erased
-- VerifiedCompilation.UCaseReduce.Equivalence.lookup-norm
d_lookup'45'norm_428 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookup'45'norm_428 = erased
-- VerifiedCompilation.UCaseReduce.Equivalence.case-constr-≡-c
d_case'45'constr'45''8801''45'c_450 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45'constr'45''8801''45'c_450 = erased
-- VerifiedCompilation.UCaseReduce.Equivalence.pw-≡
d_pw'45''8801'_470 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_pw'45''8801'_470 = erased
-- VerifiedCompilation.UCaseReduce.Equivalence.constr-≡
d_constr'45''8801'_484 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  Integer ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_constr'45''8801'_484 = erased
-- VerifiedCompilation.UCaseReduce.Equivalence.case-≡
d_case'45''8801'_492 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_case'45''8801'_492 = erased
-- VerifiedCompilation.UCaseReduce.Equivalence.complete
d_complete_506 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T__'126'__94 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_complete_506 = erased
-- VerifiedCompilation.UCaseReduce.Equivalence.complete*
d_complete'42'_508 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_complete'42'_508 ~v0 v1 v2 v3 = du_complete'42'_508 v1 v2 v3
du_complete'42'_508 ::
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_complete'42'_508 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
        -> coe v2
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    (:) v11 v12
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                           erased (coe du_complete'42'_508 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UCaseReduce.Equivalence.reduce-case
d_reduce'45'case_558 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  (MAlonzo.Code.VerifiedCompilation.UntypedViews.T_constr'7510'_944 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reduce'45'case_558 = erased
-- VerifiedCompilation.UCaseReduce.Equivalence.norm-CR
d_norm'45'CR_600 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.T_Translation_8
d_norm'45'CR_600 v0 v1
  = case coe v1 of
      MAlonzo.Code.Untyped.C_'96'_18 v2
        -> coe
             MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
             (coe MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_var_22)
      MAlonzo.Code.Untyped.C_ƛ_20 v2
        -> coe
             MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
             (coe
                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_ƛ_28
                (d_norm'45'CR_600
                   (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v2)))
      MAlonzo.Code.Untyped.C__'183'__22 v2 v3
        -> coe
             MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
             (coe
                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_app_38
                (d_norm'45'CR_600 (coe v0) (coe v2))
                (d_norm'45'CR_600 (coe v0) (coe v3)))
      MAlonzo.Code.Untyped.C_force_24 v2
        -> coe
             MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
             (coe
                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_force_44
                (d_norm'45'CR_600 (coe v0) (coe v2)))
      MAlonzo.Code.Untyped.C_delay_26 v2
        -> coe
             MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
             (coe
                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_delay_50
                (d_norm'45'CR_600 (coe v0) (coe v2)))
      MAlonzo.Code.Untyped.C_con_28 v2
        -> coe
             MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
             (coe MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_con_54)
      MAlonzo.Code.Untyped.C_constr_34 v2 v3
        -> coe
             MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
             (coe
                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_constr_62
                (d_norm'45'CR'42'_606 (coe v0) (coe v3)))
      MAlonzo.Code.Untyped.C_case_40 v2 v3
        -> let v4
                 = MAlonzo.Code.Untyped.Transform.d__'8593''42'__14
                     (\ v4 v5 -> coe du_reduce_30 v5) (coe v0) (coe v3) in
           coe
             (let v5
                    = coe
                        du_reduce_30
                        (coe
                           MAlonzo.Code.Untyped.Transform.du_'46'extendedlambda0_38
                           (\ v5 v6 -> coe du_reduce_30 v6) (coe v0) (coe v2)) in
              coe
                (let v6
                       = \ v6 ->
                           coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
                 coe
                   (let v7
                          = \ v7 ->
                              coe MAlonzo.Code.VerifiedCompilation.UntypedViews.du_'8943'_2158 in
                    coe
                      (case coe v5 of
                         MAlonzo.Code.Untyped.C_'96'_18 v8
                           -> coe
                                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
                                (coe
                                   MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_case_72
                                   (d_norm'45'CR'42'_606 (coe v0) (coe v3))
                                   (d_norm'45'CR_600 (coe v0) (coe v2)))
                         MAlonzo.Code.Untyped.C_ƛ_20 v8
                           -> coe
                                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
                                (coe
                                   MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_case_72
                                   (d_norm'45'CR'42'_606 (coe v0) (coe v3))
                                   (d_norm'45'CR_600 (coe v0) (coe v2)))
                         MAlonzo.Code.Untyped.C__'183'__22 v8 v9
                           -> coe
                                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
                                (coe
                                   MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_case_72
                                   (d_norm'45'CR'42'_606 (coe v0) (coe v3))
                                   (d_norm'45'CR_600 (coe v0) (coe v2)))
                         MAlonzo.Code.Untyped.C_force_24 v8
                           -> coe
                                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
                                (coe
                                   MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_case_72
                                   (d_norm'45'CR'42'_606 (coe v0) (coe v3))
                                   (d_norm'45'CR_600 (coe v0) (coe v2)))
                         MAlonzo.Code.Untyped.C_delay_26 v8
                           -> coe
                                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
                                (coe
                                   MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_case_72
                                   (d_norm'45'CR'42'_606 (coe v0) (coe v3))
                                   (d_norm'45'CR_600 (coe v0) (coe v2)))
                         MAlonzo.Code.Untyped.C_con_28 v8
                           -> coe
                                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
                                (coe
                                   MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_case_72
                                   (d_norm'45'CR'42'_606 (coe v0) (coe v3))
                                   (d_norm'45'CR_600 (coe v0) (coe v2)))
                         MAlonzo.Code.Untyped.C_constr_34 v8 v9
                           -> let v10
                                    = coe
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                                        (coe v6 v8) (coe v7 v9) in
                              coe
                                (case coe v10 of
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                     -> if coe v11
                                          then case coe v12 of
                                                 MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v13
                                                   -> case coe v13 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                          -> coe
                                                               seq (coe v14)
                                                               (coe
                                                                  seq (coe v15)
                                                                  (let v16
                                                                         = coe
                                                                             MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                             (coe v8) (coe v4) in
                                                                   coe
                                                                     (case coe v16 of
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                                                          -> coe
                                                                               MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_istranslation_88
                                                                               (coe
                                                                                  MAlonzo.Code.VerifiedCompilation.UCaseReduce.Inductive.C_casereduce''_218
                                                                                  v17 v9
                                                                                  (MAlonzo.Code.Untyped.Transform.d__'8593''42'__14
                                                                                     (\ v18 v19 ->
                                                                                        coe
                                                                                          du_reduce_30
                                                                                          v19)
                                                                                     (coe v0)
                                                                                     (coe v3))
                                                                                  v8
                                                                                  (d_norm'45'CR_600
                                                                                     (coe v0)
                                                                                     (coe v2))
                                                                                  (d_norm'45'CR'42'_606
                                                                                     (coe v0)
                                                                                     (coe v3)))
                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                          -> coe
                                                                               MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
                                                                               (coe
                                                                                  MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_case_72
                                                                                  (d_norm'45'CR'42'_606
                                                                                     (coe v0)
                                                                                     (coe v3))
                                                                                  (d_norm'45'CR_600
                                                                                     (coe v0)
                                                                                     (coe v2)))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)))
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                          else (let v13
                                                      = seq
                                                          (coe v12)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                             (coe v11)
                                                             (coe
                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                                coe
                                                  (case coe v13 of
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                       -> if coe v14
                                                            then case coe v15 of
                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                                                     -> case coe v16 of
                                                                          MAlonzo.Code.VerifiedCompilation.UntypedViews.C_constr'33'_954 v19 v20
                                                                            -> coe
                                                                                 seq (coe v19)
                                                                                 (coe
                                                                                    seq (coe v20)
                                                                                    (let v21
                                                                                           = coe
                                                                                               MAlonzo.Code.Untyped.CEK.du_lookup'63'_996
                                                                                               (coe
                                                                                                  v8)
                                                                                               (coe
                                                                                                  v4) in
                                                                                     coe
                                                                                       (case coe
                                                                                               v21 of
                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v22
                                                                                            -> coe
                                                                                                 MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_istranslation_88
                                                                                                 (coe
                                                                                                    MAlonzo.Code.VerifiedCompilation.UCaseReduce.Inductive.C_casereduce''_218
                                                                                                    v22
                                                                                                    v9
                                                                                                    (MAlonzo.Code.Untyped.Transform.d__'8593''42'__14
                                                                                                       (\ v23
                                                                                                          v24 ->
                                                                                                          coe
                                                                                                            du_reduce_30
                                                                                                            v24)
                                                                                                       (coe
                                                                                                          v0)
                                                                                                       (coe
                                                                                                          v3))
                                                                                                    v8
                                                                                                    (d_norm'45'CR_600
                                                                                                       (coe
                                                                                                          v0)
                                                                                                       (coe
                                                                                                          v2))
                                                                                                    (d_norm'45'CR'42'_606
                                                                                                       (coe
                                                                                                          v0)
                                                                                                       (coe
                                                                                                          v3)))
                                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                            -> coe
                                                                                                 MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
                                                                                                 (coe
                                                                                                    MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_case_72
                                                                                                    (d_norm'45'CR'42'_606
                                                                                                       (coe
                                                                                                          v0)
                                                                                                       (coe
                                                                                                          v3))
                                                                                                    (d_norm'45'CR_600
                                                                                                       (coe
                                                                                                          v0)
                                                                                                       (coe
                                                                                                          v2)))
                                                                                          _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            else coe
                                                                   seq (coe v15)
                                                                   (coe
                                                                      MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
                                                                      (coe
                                                                         MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_case_72
                                                                         (d_norm'45'CR'42'_606
                                                                            (coe v0) (coe v3))
                                                                         (d_norm'45'CR_600
                                                                            (coe v0) (coe v2))))
                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                   _ -> MAlonzo.RTE.mazUnreachableError)
                         MAlonzo.Code.Untyped.C_case_40 v8 v9
                           -> coe
                                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
                                (coe
                                   MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_case_72
                                   (d_norm'45'CR'42'_606 (coe v0) (coe v3))
                                   (d_norm'45'CR_600 (coe v0) (coe v2)))
                         MAlonzo.Code.Untyped.C_builtin_44 v8
                           -> coe
                                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
                                (coe
                                   MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_case_72
                                   (d_norm'45'CR'42'_606 (coe v0) (coe v3))
                                   (d_norm'45'CR_600 (coe v0) (coe v2)))
                         MAlonzo.Code.Untyped.C_error_46
                           -> coe
                                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
                                (coe
                                   MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_case_72
                                   (d_norm'45'CR'42'_606 (coe v0) (coe v3))
                                   (d_norm'45'CR_600 (coe v0) (coe v2)))
                         _ -> MAlonzo.RTE.mazUnreachableError))))
      MAlonzo.Code.Untyped.C_builtin_44 v2
        -> coe
             MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
             (coe
                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_builtin_76)
      MAlonzo.Code.Untyped.C_error_46
        -> coe
             MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_match_94
             (coe
                MAlonzo.Code.VerifiedCompilation.UntypedTranslation.C_error_78)
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.UCaseReduce.Equivalence.norm-CR*
d_norm'45'CR'42'_606 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_norm'45'CR'42'_606 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
             (d_norm'45'CR_600 (coe v0) (coe v2))
             (d_norm'45'CR'42'_606 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
