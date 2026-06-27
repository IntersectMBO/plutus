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

module MAlonzo.Code.Untyped.Reduction where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.NonEmpty.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.CEK
import qualified MAlonzo.Code.Untyped.RenamingSubstitution

-- Untyped.Reduction.Arity
d_Arity_4 = ()
data T_Arity_4 = C_no'45'builtin_6 | C_want_8 Integer Integer
-- Untyped.Reduction.want-injective₀
d_want'45'injective'8320'_18 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_want'45'injective'8320'_18 = erased
-- Untyped.Reduction.want-injective₁
d_want'45'injective'8321'_28 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_want'45'injective'8321'_28 = erased
-- Untyped.Reduction.interleave-error
d_interleave'45'error_32
  = error
      "MAlonzo Runtime Error: postulate evaluated: Untyped.Reduction.interleave-error"
-- Untyped.Reduction.sat
d_sat_36 ::
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> T_Arity_4
d_sat_36 ~v0 v1 = du_sat_36 v1
du_sat_36 :: MAlonzo.Code.Untyped.T__'8866'_14 -> T_Arity_4
du_sat_36 v0
  = case coe v0 of
      MAlonzo.Code.Untyped.C_'96'_18 v1 -> coe C_no'45'builtin_6
      MAlonzo.Code.Untyped.C_ƛ_20 v1 -> coe C_no'45'builtin_6
      MAlonzo.Code.Untyped.C__'183'__22 v1 v2
        -> let v3 = coe du_sat_36 (coe v1) in
           coe
             (case coe v3 of
                C_no'45'builtin_6 -> coe v3
                C_want_8 v4 v5
                  -> case coe v4 of
                       0 -> case coe v5 of
                              0 -> coe C_want_8 (coe (0 :: Integer)) (coe (0 :: Integer))
                              _ -> let v6 = subInt (coe v5) (coe (1 :: Integer)) in
                                   coe (coe C_want_8 (coe (0 :: Integer)) (coe v6))
                       _ -> coe d_interleave'45'error_32 erased
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Untyped.C_force_24 v1
        -> let v2 = coe du_sat_36 (coe v1) in
           coe
             (case coe v2 of
                C_no'45'builtin_6 -> coe v2
                C_want_8 v3 v4
                  -> case coe v3 of
                       0 -> coe seq (coe v4) (coe d_interleave'45'error_32 erased)
                       _ -> let v5 = subInt (coe v3) (coe (1 :: Integer)) in
                            coe (coe C_want_8 (coe v5) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Untyped.C_delay_26 v1 -> coe C_no'45'builtin_6
      MAlonzo.Code.Untyped.C_con_28 v1 -> coe C_no'45'builtin_6
      MAlonzo.Code.Untyped.C_constr_34 v1 v2 -> coe C_no'45'builtin_6
      MAlonzo.Code.Untyped.C_case_40 v1 v2 -> coe C_no'45'builtin_6
      MAlonzo.Code.Untyped.C_builtin_44 v1
        -> coe
             C_want_8 (coe MAlonzo.Code.Builtin.d_arity'8320'_300 (coe v1))
             (coe MAlonzo.Code.Builtin.d_arity_304 (coe v1))
      MAlonzo.Code.Untyped.C_error_46 -> coe C_no'45'builtin_6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Reduction.sat-app-step
d_sat'45'app'45'step_114 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sat'45'app'45'step_114 = erased
-- Untyped.Reduction.sat-force-step
d_sat'45'force'45'step_138 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sat'45'force'45'step_138 = erased
-- Untyped.Reduction.nat-threshold
d_nat'45'threshold_158 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_nat'45'threshold_158 = erased
-- Untyped.Reduction.Value
d_Value_180 a0 = ()
data T_Value_180
  = C_delay_184 | C_ƛ_188 | C_con_192 | C_builtin_196 |
    C_unsat'8320'_204 Integer Integer T_Value_180 |
    C_unsat'8320''8331''8321'_210 Integer T_Value_180 |
    C_unsat'8321'_218 Integer T_Value_180 T_Value_180 |
    C_constr_224 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- Untyped.Reduction.value-constr-recurse
d_value'45'constr'45'recurse_230 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  T_Value_180 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_value'45'constr'45'recurse_230 ~v0 ~v1 v2
  = du_value'45'constr'45'recurse_230 v2
du_value'45'constr'45'recurse_230 ::
  T_Value_180 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_value'45'constr'45'recurse_230 v0
  = case coe v0 of
      C_constr_224 v3
        -> case coe v3 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50 -> coe v3
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Reduction.iterApp
d_iterApp_238 ::
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_iterApp_238 ~v0 v1 v2 = du_iterApp_238 v1 v2
du_iterApp_238 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14
du_iterApp_238 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe
             du_iterApp_238
             (coe MAlonzo.Code.Untyped.C__'183'__22 (coe v0) (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Reduction.reduceBuiltin
d_reduceBuiltin_248
  = error
      "MAlonzo Runtime Error: postulate evaluated: Untyped.Reduction.reduceBuiltin"
-- Untyped.Reduction._⟶_
d__'10230'__250 a0 a1 = ()
data T__'10230'__250
  = C_ξ'8321'_258 T__'10230'__250 |
    C_ξ'8322'_266 T_Value_180 T__'10230'__250 |
    C_ξ'8323'_272 T__'10230'__250 | C_β_278 T_Value_180 |
    C_force'45'delay_282 | C_error'8321'_286 | C_error'8322'_290 |
    C_force'45'error_292 | C_sat'45'app'45'builtin_298 |
    C_sat'45'force'45'builtin_302 |
    C_case'45'constr_312 MAlonzo.Code.Untyped.T__'8866'_14 |
    C_broken'45'const_320 | C_constr'45'step_330 T__'10230'__250 |
    C_constr'45'sub'45'step_340 T__'10230'__250 |
    C_constr'45'error_346 |
    C_constr'45'sub'45'error_354 T__'10230'__250 | C_force'45'ƛ_358 |
    C_force'45'con_362 | C_force'45'constr_368 |
    C_force'45'interleave'45'error_374 Integer |
    C_app'45'interleave'45'error_384 Integer Integer |
    C_app'45'con_390 | C_app'45'delay_396 | C_app'45'constr_404 |
    C_case'45'error_408 | C_case'45'ƛ_414 | C_case'45'delay_420 |
    C_case'45'con_426 | C_case'45'builtin_432 |
    C_case'45'unsat'8320'_442 Integer Integer |
    C_case'45'unsat'8321'_450 Integer |
    C_case'45'reduce_458 T__'10230'__250
-- Untyped.Reduction._⟶*_
d__'10230''42'__460 a0 a1 = ()
data T__'10230''42'__460
  = C_refl_464 |
    C_trans_472 MAlonzo.Code.Untyped.T__'8866'_14 T__'10230'__250
                T__'10230''42'__460
-- Untyped.Reduction.tran-⟶*
d_tran'45''10230''42'_480 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T__'10230''42'__460 -> T__'10230''42'__460 -> T__'10230''42'__460
d_tran'45''10230''42'_480 ~v0 ~v1 ~v2 v3 v4
  = du_tran'45''10230''42'_480 v3 v4
du_tran'45''10230''42'_480 ::
  T__'10230''42'__460 -> T__'10230''42'__460 -> T__'10230''42'__460
du_tran'45''10230''42'_480 v0 v1
  = case coe v0 of
      C_refl_464 -> coe v1
      C_trans_472 v3 v5 v6
        -> case coe v1 of
             C_refl_464 -> coe C_trans_472 v3 v5 v6
             C_trans_472 v8 v10 v11
               -> coe
                    C_trans_472 v3 v5
                    (coe
                       du_tran'45''10230''42'_480 (coe v6) (coe C_trans_472 v8 v10 v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Reduction.irred
d_irred_496 :: MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_irred_496 = erased
-- Untyped.Reduction.value
d_value_502 :: MAlonzo.Code.Untyped.T__'8866'_14 -> ()
d_value_502 = erased
-- Untyped.Reduction.irred-constr
d_irred'45'constr_510 ::
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T__'10230'__250 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irred'45'constr_510 = erased
-- Untyped.Reduction.unsaturated
d_unsaturated_562 a0 = ()
data T_unsaturated_562
  = C_arg'45'arg_570 Integer T_Value_180 T_Value_180 |
    C_force'45'force'45'args_578 Integer Integer T_Value_180 |
    C_force'45'args_584 Integer T_Value_180
-- Untyped.Reduction.irred-unsaturated
d_irred'45'unsaturated_588
  = error
      "MAlonzo Runtime Error: postulate evaluated: Untyped.Reduction.irred-unsaturated"
-- Untyped.Reduction.V-v
d_V'45'v_592 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T_Value_180 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_V'45'v_592 ~v0 v1 = du_V'45'v_592 v1
du_V'45'v_592 ::
  T_Value_180 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_V'45'v_592 v0
  = coe
      seq (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Untyped.Reduction.V-v*
d_V'45'v'42'_596 ::
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_V'45'v'42'_596 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50 -> coe v1
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v4 v5
        -> case coe v0 of
             (:) v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                    (coe du_V'45'v_592 (coe v4)) (d_V'45'v'42'_596 (coe v7) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Reduction.value-Value
d_value'45'Value_620
  = error
      "MAlonzo Runtime Error: postulate evaluated: Untyped.Reduction.value-Value"
-- Untyped.Reduction.Progress
d_Progress_624 a0 = ()
data T_Progress_624
  = C_step_630 MAlonzo.Code.Untyped.T__'8866'_14 T__'10230'__250 |
    C_done_634 T_Value_180 | C_fail_636
-- Untyped.Reduction.progress
d_progress_640 ::
  MAlonzo.Code.Untyped.T__'8866'_14 -> T_Progress_624
d_progress_640 v0
  = case coe v0 of
      MAlonzo.Code.Untyped.C_ƛ_20 v1 -> coe C_done_634 (coe C_ƛ_188)
      MAlonzo.Code.Untyped.C__'183'__22 v1 v2
        -> let v3 = d_progress_640 (coe v1) in
           coe
             (case coe v3 of
                C_step_630 v5 v6
                  -> coe
                       C_step_630
                       (coe MAlonzo.Code.Untyped.C__'183'__22 (coe v5) (coe v2))
                       (coe C_ξ'8321'_258 v6)
                C_done_634 v5
                  -> let v6 = d_progress_640 (coe v2) in
                     coe
                       (case coe v6 of
                          C_step_630 v8 v9
                            -> coe
                                 C_step_630
                                 (coe MAlonzo.Code.Untyped.C__'183'__22 (coe v1) (coe v8))
                                 (coe C_ξ'8322'_266 v5 v9)
                          C_done_634 v8
                            -> case coe v5 of
                                 C_delay_184
                                   -> coe
                                        C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_app'45'delay_396)
                                 C_ƛ_188
                                   -> case coe v1 of
                                        MAlonzo.Code.Untyped.C_ƛ_20 v10
                                          -> coe
                                               C_step_630
                                               (MAlonzo.Code.Untyped.RenamingSubstitution.d__'91'_'93'_478
                                                  (coe (0 :: Integer)) (coe v10) (coe v2))
                                               (coe C_β_278 v8)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_con_192
                                   -> coe
                                        C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_app'45'con_390)
                                 C_builtin_196
                                   -> case coe v1 of
                                        MAlonzo.Code.Untyped.C_builtin_44 v10
                                          -> let v11
                                                   = addInt
                                                       (coe (1 :: Integer))
                                                       (coe
                                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                                          (let v11
                                                                 = \ v11 ->
                                                                     addInt
                                                                       (coe (1 :: Integer))
                                                                       (coe v11) in
                                                           coe (coe (\ v12 -> v11)))
                                                          (coe (0 :: Integer))
                                                          (coe
                                                             MAlonzo.Code.Data.List.NonEmpty.Base.d_tail_32
                                                             (coe
                                                                MAlonzo.Code.Builtin.Signature.d_args_84
                                                                (coe
                                                                   MAlonzo.Code.Builtin.d_signature_298
                                                                   (coe v10))))) in
                                             coe
                                               (let v12
                                                      = addInt
                                                          (coe
                                                             MAlonzo.Code.Builtin.Signature.d_fv'9839'_82
                                                             (coe
                                                                MAlonzo.Code.Builtin.d_signature_298
                                                                (coe v10)))
                                                          (coe
                                                             MAlonzo.Code.Builtin.Signature.d_fv'8902'_80
                                                             (coe
                                                                MAlonzo.Code.Builtin.d_signature_298
                                                                (coe v10))) in
                                                coe
                                                  (case coe v12 of
                                                     0 -> case coe v11 of
                                                            1 -> coe
                                                                   C_step_630
                                                                   (coe
                                                                      d_reduceBuiltin_248
                                                                      (0 :: Integer) v0)
                                                                   (coe C_sat'45'app'45'builtin_298)
                                                            _ -> let v13
                                                                       = subInt
                                                                           (coe v11)
                                                                           (coe (2 :: Integer)) in
                                                                 coe
                                                                   (coe
                                                                      C_done_634
                                                                      (coe
                                                                         C_unsat'8321'_218 v13 v5
                                                                         v8))
                                                     _ -> let v13
                                                                = subInt
                                                                    (coe v12)
                                                                    (coe (1 :: Integer)) in
                                                          coe
                                                            (coe
                                                               C_step_630
                                                               (coe MAlonzo.Code.Untyped.C_error_46)
                                                               (coe
                                                                  C_app'45'interleave'45'error_384
                                                                  v13 v11))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_unsat'8320'_204 v10 v11 v13
                                   -> coe
                                        C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_app'45'interleave'45'error_384 v10 v11)
                                 C_unsat'8320''8331''8321'_210 v10 v12
                                   -> case coe v1 of
                                        MAlonzo.Code.Untyped.C_force_24 v13
                                          -> let v14 = coe du_sat_36 (coe v13) in
                                             coe
                                               (case coe v14 of
                                                  C_no'45'builtin_6
                                                    -> case coe v14 of
                                                         C_no'45'builtin_6
                                                           -> coe
                                                                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                erased
                                                         C_want_8 v15 v16
                                                           -> case coe v15 of
                                                                0 -> case coe v16 of
                                                                       0 -> coe
                                                                              C_step_630
                                                                              (coe
                                                                                 MAlonzo.Code.Untyped.C__'183'__22
                                                                                 (coe
                                                                                    d_reduceBuiltin_248
                                                                                    (0 :: Integer)
                                                                                    v1)
                                                                                 (coe v2))
                                                                              (coe
                                                                                 C_ξ'8321'_258
                                                                                 (coe
                                                                                    C_sat'45'force'45'builtin_302))
                                                                       1 -> coe
                                                                              C_step_630
                                                                              (coe
                                                                                 d_reduceBuiltin_248
                                                                                 (0 :: Integer) v0)
                                                                              (coe
                                                                                 C_sat'45'app'45'builtin_298)
                                                                       _ -> let v17
                                                                                  = subInt
                                                                                      (coe v16)
                                                                                      (coe
                                                                                         (2 ::
                                                                                            Integer)) in
                                                                            coe
                                                                              (coe
                                                                                 C_done_634
                                                                                 (coe
                                                                                    C_unsat'8321'_218
                                                                                    v17 v5 v8))
                                                                _ -> let v17
                                                                           = subInt
                                                                               (coe v15)
                                                                               (coe
                                                                                  (1 :: Integer)) in
                                                                     coe
                                                                       (coe
                                                                          C_step_630
                                                                          (coe
                                                                             MAlonzo.Code.Untyped.C_error_46)
                                                                          (coe
                                                                             C_app'45'interleave'45'error_384
                                                                             v17 v16))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  C_want_8 v15 v16
                                                    -> case coe v15 of
                                                         0 -> let v17
                                                                    = seq
                                                                        (coe v16)
                                                                        (coe
                                                                           d_interleave'45'error_32
                                                                           erased) in
                                                              coe
                                                                (case coe v17 of
                                                                   C_no'45'builtin_6
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                          erased
                                                                   C_want_8 v18 v19
                                                                     -> case coe v18 of
                                                                          0 -> case coe v19 of
                                                                                 0 -> coe
                                                                                        C_step_630
                                                                                        (coe
                                                                                           MAlonzo.Code.Untyped.C__'183'__22
                                                                                           (coe
                                                                                              d_reduceBuiltin_248
                                                                                              (0 ::
                                                                                                 Integer)
                                                                                              v1)
                                                                                           (coe v2))
                                                                                        (coe
                                                                                           C_ξ'8321'_258
                                                                                           (coe
                                                                                              C_sat'45'force'45'builtin_302))
                                                                                 1 -> coe
                                                                                        C_step_630
                                                                                        (coe
                                                                                           d_reduceBuiltin_248
                                                                                           (0 ::
                                                                                              Integer)
                                                                                           v0)
                                                                                        (coe
                                                                                           C_sat'45'app'45'builtin_298)
                                                                                 _ -> let v20
                                                                                            = subInt
                                                                                                (coe
                                                                                                   v19)
                                                                                                (coe
                                                                                                   (2 ::
                                                                                                      Integer)) in
                                                                                      coe
                                                                                        (coe
                                                                                           C_done_634
                                                                                           (coe
                                                                                              C_unsat'8321'_218
                                                                                              v20 v5
                                                                                              v8))
                                                                          _ -> let v20
                                                                                     = subInt
                                                                                         (coe v18)
                                                                                         (coe
                                                                                            (1 ::
                                                                                               Integer)) in
                                                                               coe
                                                                                 (coe
                                                                                    C_step_630
                                                                                    (coe
                                                                                       MAlonzo.Code.Untyped.C_error_46)
                                                                                    (coe
                                                                                       C_app'45'interleave'45'error_384
                                                                                       v20 v19))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         1 -> case coe v16 of
                                                                0 -> coe
                                                                       C_step_630
                                                                       (coe
                                                                          MAlonzo.Code.Untyped.C__'183'__22
                                                                          (coe
                                                                             d_reduceBuiltin_248
                                                                             (0 :: Integer) v1)
                                                                          (coe v2))
                                                                       (coe
                                                                          C_ξ'8321'_258
                                                                          (coe
                                                                             C_sat'45'force'45'builtin_302))
                                                                1 -> coe
                                                                       C_step_630
                                                                       (coe
                                                                          d_reduceBuiltin_248
                                                                          (0 :: Integer) v0)
                                                                       (coe
                                                                          C_sat'45'app'45'builtin_298)
                                                                _ -> let v17
                                                                           = subInt
                                                                               (coe v16)
                                                                               (coe
                                                                                  (2 :: Integer)) in
                                                                     coe
                                                                       (coe
                                                                          C_done_634
                                                                          (coe
                                                                             C_unsat'8321'_218 v17
                                                                             v5 v8))
                                                         _ -> let v17
                                                                    = subInt
                                                                        (coe v15)
                                                                        (coe (2 :: Integer)) in
                                                              coe
                                                                (coe
                                                                   C_step_630
                                                                   (coe
                                                                      MAlonzo.Code.Untyped.C_error_46)
                                                                   (coe
                                                                      C_app'45'interleave'45'error_384
                                                                      v17 v16))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_unsat'8321'_218 v11 v13 v14
                                   -> case coe v1 of
                                        MAlonzo.Code.Untyped.C__'183'__22 v15 v16
                                          -> let v17 = coe du_sat_36 (coe v15) in
                                             coe
                                               (case coe v17 of
                                                  C_no'45'builtin_6
                                                    -> case coe v17 of
                                                         C_no'45'builtin_6
                                                           -> coe
                                                                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                erased
                                                         C_want_8 v18 v19
                                                           -> case coe v18 of
                                                                0 -> case coe v19 of
                                                                       0 -> coe
                                                                              C_step_630
                                                                              (coe
                                                                                 MAlonzo.Code.Untyped.C__'183'__22
                                                                                 (coe
                                                                                    d_reduceBuiltin_248
                                                                                    (0 :: Integer)
                                                                                    v1)
                                                                                 (coe v2))
                                                                              (coe
                                                                                 C_ξ'8321'_258
                                                                                 (coe
                                                                                    C_sat'45'app'45'builtin_298))
                                                                       1 -> coe
                                                                              C_step_630
                                                                              (coe
                                                                                 d_reduceBuiltin_248
                                                                                 (0 :: Integer) v0)
                                                                              (coe
                                                                                 C_sat'45'app'45'builtin_298)
                                                                       _ -> let v20
                                                                                  = subInt
                                                                                      (coe v19)
                                                                                      (coe
                                                                                         (2 ::
                                                                                            Integer)) in
                                                                            coe
                                                                              (coe
                                                                                 C_done_634
                                                                                 (coe
                                                                                    C_unsat'8321'_218
                                                                                    v20 v5 v8))
                                                                _ -> let v20
                                                                           = subInt
                                                                               (coe v18)
                                                                               (coe
                                                                                  (1 :: Integer)) in
                                                                     coe
                                                                       (coe
                                                                          C_step_630
                                                                          (coe
                                                                             MAlonzo.Code.Untyped.C_error_46)
                                                                          (coe
                                                                             C_app'45'interleave'45'error_384
                                                                             v20 v19))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  C_want_8 v18 v19
                                                    -> case coe v18 of
                                                         0 -> case coe v19 of
                                                                0 -> let v20 = 0 :: Integer in
                                                                     coe
                                                                       (let v21 = 0 :: Integer in
                                                                        coe
                                                                          (case coe v20 of
                                                                             0 -> case coe v21 of
                                                                                    0 -> coe
                                                                                           C_step_630
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C__'183'__22
                                                                                              (coe
                                                                                                 d_reduceBuiltin_248
                                                                                                 (0 ::
                                                                                                    Integer)
                                                                                                 v1)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_ξ'8321'_258
                                                                                              (coe
                                                                                                 C_sat'45'app'45'builtin_298))
                                                                                    1 -> coe
                                                                                           C_step_630
                                                                                           (coe
                                                                                              d_reduceBuiltin_248
                                                                                              (1 ::
                                                                                                 Integer)
                                                                                              v0)
                                                                                           (coe
                                                                                              C_sat'45'app'45'builtin_298)
                                                                                    _ -> let v22
                                                                                               = -2 ::
                                                                                                   Integer in
                                                                                         coe
                                                                                           (coe
                                                                                              C_done_634
                                                                                              (coe
                                                                                                 C_unsat'8321'_218
                                                                                                 v22
                                                                                                 v5
                                                                                                 v8))
                                                                             _ -> let v22
                                                                                        = -1 ::
                                                                                            Integer in
                                                                                  coe
                                                                                    (coe
                                                                                       C_step_630
                                                                                       (coe
                                                                                          MAlonzo.Code.Untyped.C_error_46)
                                                                                       (coe
                                                                                          C_app'45'interleave'45'error_384
                                                                                          v22
                                                                                          v21))))
                                                                _ -> let v20
                                                                           = subInt
                                                                               (coe v19)
                                                                               (coe
                                                                                  (1 :: Integer)) in
                                                                     coe
                                                                       (let v21 = 0 :: Integer in
                                                                        coe
                                                                          (case coe v21 of
                                                                             0 -> case coe v19 of
                                                                                    1 -> coe
                                                                                           C_step_630
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C__'183'__22
                                                                                              (coe
                                                                                                 d_reduceBuiltin_248
                                                                                                 (0 ::
                                                                                                    Integer)
                                                                                                 v1)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_ξ'8321'_258
                                                                                              (coe
                                                                                                 C_sat'45'app'45'builtin_298))
                                                                                    2 -> coe
                                                                                           C_step_630
                                                                                           (coe
                                                                                              d_reduceBuiltin_248
                                                                                              (0 ::
                                                                                                 Integer)
                                                                                              v0)
                                                                                           (coe
                                                                                              C_sat'45'app'45'builtin_298)
                                                                                    _ -> let v22
                                                                                               = subInt
                                                                                                   (coe
                                                                                                      v19)
                                                                                                   (coe
                                                                                                      (3 ::
                                                                                                         Integer)) in
                                                                                         coe
                                                                                           (coe
                                                                                              C_done_634
                                                                                              (coe
                                                                                                 C_unsat'8321'_218
                                                                                                 v22
                                                                                                 v5
                                                                                                 v8))
                                                                             _ -> let v22
                                                                                        = -1 ::
                                                                                            Integer in
                                                                                  coe
                                                                                    (coe
                                                                                       C_step_630
                                                                                       (coe
                                                                                          MAlonzo.Code.Untyped.C_error_46)
                                                                                       (coe
                                                                                          C_app'45'interleave'45'error_384
                                                                                          v22
                                                                                          v20))))
                                                         _ -> let v20
                                                                    = coe
                                                                        d_interleave'45'error_32
                                                                        erased in
                                                              coe
                                                                (case coe v20 of
                                                                   C_no'45'builtin_6
                                                                     -> coe
                                                                          MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                          erased
                                                                   C_want_8 v21 v22
                                                                     -> case coe v21 of
                                                                          0 -> case coe v22 of
                                                                                 0 -> coe
                                                                                        C_step_630
                                                                                        (coe
                                                                                           MAlonzo.Code.Untyped.C__'183'__22
                                                                                           (coe
                                                                                              d_reduceBuiltin_248
                                                                                              (0 ::
                                                                                                 Integer)
                                                                                              v1)
                                                                                           (coe v2))
                                                                                        (coe
                                                                                           C_ξ'8321'_258
                                                                                           (coe
                                                                                              C_sat'45'app'45'builtin_298))
                                                                                 1 -> coe
                                                                                        C_step_630
                                                                                        (coe
                                                                                           d_reduceBuiltin_248
                                                                                           (0 ::
                                                                                              Integer)
                                                                                           v0)
                                                                                        (coe
                                                                                           C_sat'45'app'45'builtin_298)
                                                                                 _ -> let v23
                                                                                            = subInt
                                                                                                (coe
                                                                                                   v22)
                                                                                                (coe
                                                                                                   (2 ::
                                                                                                      Integer)) in
                                                                                      coe
                                                                                        (coe
                                                                                           C_done_634
                                                                                           (coe
                                                                                              C_unsat'8321'_218
                                                                                              v23 v5
                                                                                              v8))
                                                                          _ -> let v23
                                                                                     = subInt
                                                                                         (coe v21)
                                                                                         (coe
                                                                                            (1 ::
                                                                                               Integer)) in
                                                                               coe
                                                                                 (coe
                                                                                    C_step_630
                                                                                    (coe
                                                                                       MAlonzo.Code.Untyped.C_error_46)
                                                                                    (coe
                                                                                       C_app'45'interleave'45'error_384
                                                                                       v23 v22))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_constr_224 v11
                                   -> coe
                                        C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_app'45'constr_404)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          C_fail_636
                            -> coe
                                 C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                                 (coe C_error'8322'_290)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_fail_636
                  -> coe
                       C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                       (coe C_error'8321'_286)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Untyped.C_force_24 v1
        -> let v2 = d_progress_640 (coe v1) in
           coe
             (case coe v2 of
                C_step_630 v4 v5
                  -> coe
                       C_step_630 (coe MAlonzo.Code.Untyped.C_force_24 (coe v4))
                       (coe C_ξ'8323'_272 v5)
                C_done_634 v4
                  -> let v5 = coe du_sat_36 (coe v1) in
                     coe
                       (case coe v5 of
                          C_no'45'builtin_6
                            -> case coe v1 of
                                 MAlonzo.Code.Untyped.C_ƛ_20 v6
                                   -> coe
                                        C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_force'45'ƛ_358)
                                 MAlonzo.Code.Untyped.C__'183'__22 v6 v7
                                   -> coe
                                        seq (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                           erased)
                                 MAlonzo.Code.Untyped.C_force_24 v6
                                   -> coe
                                        seq (coe v4)
                                        (coe
                                           MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                           erased)
                                 MAlonzo.Code.Untyped.C_delay_26 v6
                                   -> coe C_step_630 v6 (coe C_force'45'delay_282)
                                 MAlonzo.Code.Untyped.C_con_28 v6
                                   -> coe
                                        C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_force'45'con_362)
                                 MAlonzo.Code.Untyped.C_constr_34 v6 v7
                                   -> coe
                                        C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_force'45'constr_368)
                                 MAlonzo.Code.Untyped.C_error_46
                                   -> coe C_step_630 v1 (coe C_force'45'error_292)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          C_want_8 v6 v7
                            -> case coe v6 of
                                 0 -> coe
                                        C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_force'45'interleave'45'error_374 v7)
                                 1 -> case coe v7 of
                                        0 -> coe
                                               C_step_630
                                               (coe d_reduceBuiltin_248 (0 :: Integer) v0)
                                               (coe C_sat'45'force'45'builtin_302)
                                        _ -> let v8 = subInt (coe v7) (coe (1 :: Integer)) in
                                             coe
                                               (coe
                                                  C_done_634
                                                  (coe C_unsat'8320''8331''8321'_210 v8 v4))
                                 _ -> let v8 = subInt (coe v6) (coe (2 :: Integer)) in
                                      coe (coe C_done_634 (coe C_unsat'8320'_204 v8 v7 v4))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_fail_636
                  -> coe
                       C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                       (coe C_force'45'error_292)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Untyped.C_delay_26 v1
        -> coe C_done_634 (coe C_delay_184)
      MAlonzo.Code.Untyped.C_con_28 v1 -> coe C_done_634 (coe C_con_192)
      MAlonzo.Code.Untyped.C_constr_34 v1 v2
        -> case coe v2 of
             []
               -> coe
                    C_done_634
                    (coe
                       C_constr_224
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             (:) v3 v4
               -> let v5 = d_progress_640 (coe v3) in
                  coe
                    (case coe v5 of
                       C_step_630 v7 v8
                         -> coe
                              C_step_630
                              (coe
                                 MAlonzo.Code.Untyped.C_constr_34 (coe v1)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7) (coe v4)))
                              (coe C_constr'45'step_330 v8)
                       C_done_634 v7
                         -> let v8
                                  = d_progress_640
                                      (coe MAlonzo.Code.Untyped.C_constr_34 (coe v1) (coe v4)) in
                            coe
                              (case coe v8 of
                                 C_step_630 v10 v11
                                   -> case coe v11 of
                                        C_constr'45'step_330 v16
                                          -> case coe v4 of
                                               (:) v17 v18
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Untyped.C_constr_34 v19 v20
                                                        -> case coe v20 of
                                                             (:) v21 v22
                                                               -> coe
                                                                    C_step_630
                                                                    (coe
                                                                       MAlonzo.Code.Untyped.C_constr_34
                                                                       (coe v1)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe v3)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe v21) (coe v18))))
                                                                    (coe
                                                                       C_constr'45'sub'45'step_340
                                                                       (coe
                                                                          C_constr'45'step_330 v16))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        C_constr'45'sub'45'step_340 v16
                                          -> case coe v4 of
                                               (:) v17 v18
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Untyped.C_constr_34 v19 v20
                                                        -> case coe v20 of
                                                             (:) v21 v22
                                                               -> coe
                                                                    C_step_630
                                                                    (coe
                                                                       MAlonzo.Code.Untyped.C_constr_34
                                                                       (coe v1)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                          (coe v3)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe v17) (coe v22))))
                                                                    (coe
                                                                       C_constr'45'sub'45'step_340
                                                                       (coe
                                                                          C_constr'45'sub'45'step_340
                                                                          v16))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        C_constr'45'error_346
                                          -> coe
                                               C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                                               (coe
                                                  C_constr'45'sub'45'error_354
                                                  (coe C_constr'45'error_346))
                                        C_constr'45'sub'45'error_354 v15
                                          -> coe
                                               C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                                               (coe
                                                  C_constr'45'sub'45'error_354
                                                  (coe C_constr'45'sub'45'error_354 v15))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_done_634 v10
                                   -> coe
                                        C_done_634
                                        (coe
                                           C_constr_224
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                              v7 (coe du_value'45'constr'45'recurse_230 (coe v10))))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_fail_636
                         -> coe
                              C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                              (coe C_constr'45'error_346)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.C_case_40 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Untyped.C_ƛ_20 v3
               -> coe
                    C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                    (coe C_case'45'ƛ_414)
             MAlonzo.Code.Untyped.C__'183'__22 v3 v4
               -> let v5 = d_progress_640 (coe v3) in
                  coe
                    (case coe v5 of
                       C_step_630 v7 v8
                         -> let v9
                                  = coe MAlonzo.Code.Untyped.C__'183'__22 (coe v7) (coe v4) in
                            coe
                              (let v10 = coe C_ξ'8321'_258 v8 in
                               coe
                                 (coe
                                    C_step_630
                                    (coe MAlonzo.Code.Untyped.C_case_40 (coe v9) (coe v2))
                                    (coe C_case'45'reduce_458 v10)))
                       C_done_634 v7
                         -> let v8 = d_progress_640 (coe v4) in
                            coe
                              (case coe v8 of
                                 C_step_630 v10 v11
                                   -> let v12
                                            = coe
                                                MAlonzo.Code.Untyped.C__'183'__22 (coe v3)
                                                (coe v10) in
                                      coe
                                        (let v13 = coe C_ξ'8322'_266 v7 v11 in
                                         coe
                                           (coe
                                              C_step_630
                                              (coe
                                                 MAlonzo.Code.Untyped.C_case_40 (coe v12) (coe v2))
                                              (coe C_case'45'reduce_458 v13)))
                                 C_done_634 v10
                                   -> case coe v7 of
                                        C_delay_184
                                          -> let v12 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v13 = coe C_app'45'delay_396 in
                                                coe
                                                  (coe
                                                     C_step_630
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v12)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_458 v13)))
                                        C_ƛ_188
                                          -> case coe v3 of
                                               MAlonzo.Code.Untyped.C_ƛ_20 v12
                                                 -> let v13
                                                          = MAlonzo.Code.Untyped.RenamingSubstitution.d__'91'_'93'_478
                                                              (coe (0 :: Integer)) (coe v12)
                                                              (coe v4) in
                                                    coe
                                                      (let v14 = coe C_β_278 v10 in
                                                       coe
                                                         (coe
                                                            C_step_630
                                                            (coe
                                                               MAlonzo.Code.Untyped.C_case_40
                                                               (coe v13) (coe v2))
                                                            (coe C_case'45'reduce_458 v14)))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        C_con_192
                                          -> let v12 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v13 = coe C_app'45'con_390 in
                                                coe
                                                  (coe
                                                     C_step_630
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v12)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_458 v13)))
                                        C_builtin_196
                                          -> case coe v3 of
                                               MAlonzo.Code.Untyped.C_builtin_44 v12
                                                 -> let v13
                                                          = addInt
                                                              (coe (1 :: Integer))
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (let v13
                                                                        = \ v13 ->
                                                                            addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe v13) in
                                                                  coe (coe (\ v14 -> v13)))
                                                                 (coe (0 :: Integer))
                                                                 (coe
                                                                    MAlonzo.Code.Data.List.NonEmpty.Base.d_tail_32
                                                                    (coe
                                                                       MAlonzo.Code.Builtin.Signature.d_args_84
                                                                       (coe
                                                                          MAlonzo.Code.Builtin.d_signature_298
                                                                          (coe v12))))) in
                                                    coe
                                                      (let v14
                                                             = addInt
                                                                 (coe
                                                                    MAlonzo.Code.Builtin.Signature.d_fv'9839'_82
                                                                    (coe
                                                                       MAlonzo.Code.Builtin.d_signature_298
                                                                       (coe v12)))
                                                                 (coe
                                                                    MAlonzo.Code.Builtin.Signature.d_fv'8902'_80
                                                                    (coe
                                                                       MAlonzo.Code.Builtin.d_signature_298
                                                                       (coe v12))) in
                                                       coe
                                                         (case coe v14 of
                                                            0 -> case coe v13 of
                                                                   1 -> let v15
                                                                              = coe
                                                                                  d_reduceBuiltin_248
                                                                                  (0 :: Integer)
                                                                                  v1 in
                                                                        coe
                                                                          (let v16
                                                                                 = coe
                                                                                     C_sat'45'app'45'builtin_298 in
                                                                           coe
                                                                             (coe
                                                                                C_step_630
                                                                                (coe
                                                                                   MAlonzo.Code.Untyped.C_case_40
                                                                                   (coe v15)
                                                                                   (coe v2))
                                                                                (coe
                                                                                   C_case'45'reduce_458
                                                                                   v16)))
                                                                   _ -> let v15
                                                                              = subInt
                                                                                  (coe v13)
                                                                                  (coe
                                                                                     (2 ::
                                                                                        Integer)) in
                                                                        coe
                                                                          (coe
                                                                             C_step_630
                                                                             (coe
                                                                                MAlonzo.Code.Untyped.C_error_46)
                                                                             (coe
                                                                                C_case'45'unsat'8321'_450
                                                                                v15))
                                                            _ -> let v15
                                                                       = subInt
                                                                           (coe v14)
                                                                           (coe (1 :: Integer)) in
                                                                 coe
                                                                   (let v16
                                                                          = coe
                                                                              MAlonzo.Code.Untyped.C_error_46 in
                                                                    coe
                                                                      (let v17
                                                                             = coe
                                                                                 C_app'45'interleave'45'error_384
                                                                                 v15 v13 in
                                                                       coe
                                                                         (coe
                                                                            C_step_630
                                                                            (coe
                                                                               MAlonzo.Code.Untyped.C_case_40
                                                                               (coe v16) (coe v2))
                                                                            (coe
                                                                               C_case'45'reduce_458
                                                                               v17))))))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        C_unsat'8320'_204 v12 v13 v15
                                          -> let v16 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v17
                                                      = coe
                                                          C_app'45'interleave'45'error_384 v12
                                                          v13 in
                                                coe
                                                  (coe
                                                     C_step_630
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v16)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_458 v17)))
                                        C_unsat'8320''8331''8321'_210 v12 v14
                                          -> case coe v3 of
                                               MAlonzo.Code.Untyped.C_force_24 v15
                                                 -> let v16 = coe du_sat_36 (coe v15) in
                                                    coe
                                                      (case coe v16 of
                                                         C_no'45'builtin_6
                                                           -> case coe v16 of
                                                                C_no'45'builtin_6
                                                                  -> let v17
                                                                           = coe
                                                                               MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                               erased in
                                                                     coe
                                                                       (case coe v17 of
                                                                          C_step_630 v19 v20
                                                                            -> coe
                                                                                 C_step_630
                                                                                 (coe
                                                                                    MAlonzo.Code.Untyped.C_case_40
                                                                                    (coe v19)
                                                                                    (coe v2))
                                                                                 (coe
                                                                                    C_case'45'reduce_458
                                                                                    v20)
                                                                          C_done_634 v19
                                                                            -> case coe v19 of
                                                                                 C_unsat'8321'_218 v22 v24 v25
                                                                                   -> coe
                                                                                        C_step_630
                                                                                        (coe
                                                                                           MAlonzo.Code.Untyped.C_error_46)
                                                                                        (coe
                                                                                           C_case'45'unsat'8321'_450
                                                                                           v22)
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                C_want_8 v17 v18
                                                                  -> case coe v17 of
                                                                       0 -> case coe v18 of
                                                                              0 -> let v19
                                                                                         = coe
                                                                                             MAlonzo.Code.Untyped.C__'183'__22
                                                                                             (coe
                                                                                                d_reduceBuiltin_248
                                                                                                (0 ::
                                                                                                   Integer)
                                                                                                v3)
                                                                                             (coe
                                                                                                v4) in
                                                                                   coe
                                                                                     (let v20
                                                                                            = coe
                                                                                                C_ξ'8321'_258
                                                                                                (coe
                                                                                                   C_sat'45'force'45'builtin_302) in
                                                                                      coe
                                                                                        (coe
                                                                                           C_step_630
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C_case_40
                                                                                              (coe
                                                                                                 v19)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_case'45'reduce_458
                                                                                              v20)))
                                                                              1 -> let v19
                                                                                         = coe
                                                                                             d_reduceBuiltin_248
                                                                                             (0 ::
                                                                                                Integer)
                                                                                             v1 in
                                                                                   coe
                                                                                     (let v20
                                                                                            = coe
                                                                                                C_sat'45'app'45'builtin_298 in
                                                                                      coe
                                                                                        (coe
                                                                                           C_step_630
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C_case_40
                                                                                              (coe
                                                                                                 v19)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_case'45'reduce_458
                                                                                              v20)))
                                                                              _ -> let v19
                                                                                         = subInt
                                                                                             (coe
                                                                                                v18)
                                                                                             (coe
                                                                                                (2 ::
                                                                                                   Integer)) in
                                                                                   coe
                                                                                     (coe
                                                                                        C_step_630
                                                                                        (coe
                                                                                           MAlonzo.Code.Untyped.C_error_46)
                                                                                        (coe
                                                                                           C_case'45'unsat'8321'_450
                                                                                           v19))
                                                                       _ -> let v19
                                                                                  = subInt
                                                                                      (coe v17)
                                                                                      (coe
                                                                                         (1 ::
                                                                                            Integer)) in
                                                                            coe
                                                                              (let v20
                                                                                     = coe
                                                                                         MAlonzo.Code.Untyped.C_error_46 in
                                                                               coe
                                                                                 (let v21
                                                                                        = coe
                                                                                            C_app'45'interleave'45'error_384
                                                                                            v19
                                                                                            v18 in
                                                                                  coe
                                                                                    (coe
                                                                                       C_step_630
                                                                                       (coe
                                                                                          MAlonzo.Code.Untyped.C_case_40
                                                                                          (coe v20)
                                                                                          (coe v2))
                                                                                       (coe
                                                                                          C_case'45'reduce_458
                                                                                          v21))))
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         C_want_8 v17 v18
                                                           -> case coe v17 of
                                                                0 -> let v19
                                                                           = seq
                                                                               (coe v18)
                                                                               (coe
                                                                                  d_interleave'45'error_32
                                                                                  erased) in
                                                                     coe
                                                                       (case coe v19 of
                                                                          C_no'45'builtin_6
                                                                            -> let v20
                                                                                     = coe
                                                                                         MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                         erased in
                                                                               coe
                                                                                 (case coe v20 of
                                                                                    C_step_630 v22 v23
                                                                                      -> coe
                                                                                           C_step_630
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C_case_40
                                                                                              (coe
                                                                                                 v22)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_case'45'reduce_458
                                                                                              v23)
                                                                                    C_done_634 v22
                                                                                      -> case coe
                                                                                                v22 of
                                                                                           C_unsat'8321'_218 v25 v27 v28
                                                                                             -> coe
                                                                                                  C_step_630
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Untyped.C_error_46)
                                                                                                  (coe
                                                                                                     C_case'45'unsat'8321'_450
                                                                                                     v25)
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          C_want_8 v20 v21
                                                                            -> case coe v20 of
                                                                                 0 -> case coe
                                                                                             v21 of
                                                                                        0 -> let v22
                                                                                                   = coe
                                                                                                       MAlonzo.Code.Untyped.C__'183'__22
                                                                                                       (coe
                                                                                                          d_reduceBuiltin_248
                                                                                                          (0 ::
                                                                                                             Integer)
                                                                                                          v3)
                                                                                                       (coe
                                                                                                          v4) in
                                                                                             coe
                                                                                               (let v23
                                                                                                      = coe
                                                                                                          C_ξ'8321'_258
                                                                                                          (coe
                                                                                                             C_sat'45'force'45'builtin_302) in
                                                                                                coe
                                                                                                  (coe
                                                                                                     C_step_630
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Untyped.C_case_40
                                                                                                        (coe
                                                                                                           v22)
                                                                                                        (coe
                                                                                                           v2))
                                                                                                     (coe
                                                                                                        C_case'45'reduce_458
                                                                                                        v23)))
                                                                                        1 -> let v22
                                                                                                   = coe
                                                                                                       d_reduceBuiltin_248
                                                                                                       (0 ::
                                                                                                          Integer)
                                                                                                       v1 in
                                                                                             coe
                                                                                               (let v23
                                                                                                      = coe
                                                                                                          C_sat'45'app'45'builtin_298 in
                                                                                                coe
                                                                                                  (coe
                                                                                                     C_step_630
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Untyped.C_case_40
                                                                                                        (coe
                                                                                                           v22)
                                                                                                        (coe
                                                                                                           v2))
                                                                                                     (coe
                                                                                                        C_case'45'reduce_458
                                                                                                        v23)))
                                                                                        _ -> let v22
                                                                                                   = subInt
                                                                                                       (coe
                                                                                                          v21)
                                                                                                       (coe
                                                                                                          (2 ::
                                                                                                             Integer)) in
                                                                                             coe
                                                                                               (coe
                                                                                                  C_step_630
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Untyped.C_error_46)
                                                                                                  (coe
                                                                                                     C_case'45'unsat'8321'_450
                                                                                                     v22))
                                                                                 _ -> let v22
                                                                                            = subInt
                                                                                                (coe
                                                                                                   v20)
                                                                                                (coe
                                                                                                   (1 ::
                                                                                                      Integer)) in
                                                                                      coe
                                                                                        (let v23
                                                                                               = coe
                                                                                                   MAlonzo.Code.Untyped.C_error_46 in
                                                                                         coe
                                                                                           (let v24
                                                                                                  = coe
                                                                                                      C_app'45'interleave'45'error_384
                                                                                                      v22
                                                                                                      v21 in
                                                                                            coe
                                                                                              (coe
                                                                                                 C_step_630
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Untyped.C_case_40
                                                                                                    (coe
                                                                                                       v23)
                                                                                                    (coe
                                                                                                       v2))
                                                                                                 (coe
                                                                                                    C_case'45'reduce_458
                                                                                                    v24))))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                1 -> case coe v18 of
                                                                       0 -> let v19
                                                                                  = coe
                                                                                      MAlonzo.Code.Untyped.C__'183'__22
                                                                                      (coe
                                                                                         d_reduceBuiltin_248
                                                                                         (0 ::
                                                                                            Integer)
                                                                                         v3)
                                                                                      (coe v4) in
                                                                            coe
                                                                              (let v20
                                                                                     = coe
                                                                                         C_ξ'8321'_258
                                                                                         (coe
                                                                                            C_sat'45'force'45'builtin_302) in
                                                                               coe
                                                                                 (coe
                                                                                    C_step_630
                                                                                    (coe
                                                                                       MAlonzo.Code.Untyped.C_case_40
                                                                                       (coe v19)
                                                                                       (coe v2))
                                                                                    (coe
                                                                                       C_case'45'reduce_458
                                                                                       v20)))
                                                                       1 -> let v19
                                                                                  = coe
                                                                                      d_reduceBuiltin_248
                                                                                      (0 :: Integer)
                                                                                      v1 in
                                                                            coe
                                                                              (let v20
                                                                                     = coe
                                                                                         C_sat'45'app'45'builtin_298 in
                                                                               coe
                                                                                 (coe
                                                                                    C_step_630
                                                                                    (coe
                                                                                       MAlonzo.Code.Untyped.C_case_40
                                                                                       (coe v19)
                                                                                       (coe v2))
                                                                                    (coe
                                                                                       C_case'45'reduce_458
                                                                                       v20)))
                                                                       _ -> let v19
                                                                                  = subInt
                                                                                      (coe v18)
                                                                                      (coe
                                                                                         (2 ::
                                                                                            Integer)) in
                                                                            coe
                                                                              (coe
                                                                                 C_step_630
                                                                                 (coe
                                                                                    MAlonzo.Code.Untyped.C_error_46)
                                                                                 (coe
                                                                                    C_case'45'unsat'8321'_450
                                                                                    v19))
                                                                _ -> let v19
                                                                           = subInt
                                                                               (coe v17)
                                                                               (coe
                                                                                  (2 :: Integer)) in
                                                                     coe
                                                                       (let v20
                                                                              = coe
                                                                                  MAlonzo.Code.Untyped.C_error_46 in
                                                                        coe
                                                                          (let v21
                                                                                 = coe
                                                                                     C_app'45'interleave'45'error_384
                                                                                     v19 v18 in
                                                                           coe
                                                                             (coe
                                                                                C_step_630
                                                                                (coe
                                                                                   MAlonzo.Code.Untyped.C_case_40
                                                                                   (coe v20)
                                                                                   (coe v2))
                                                                                (coe
                                                                                   C_case'45'reduce_458
                                                                                   v21))))
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        C_unsat'8321'_218 v13 v15 v16
                                          -> case coe v3 of
                                               MAlonzo.Code.Untyped.C__'183'__22 v17 v18
                                                 -> let v19 = coe du_sat_36 (coe v17) in
                                                    coe
                                                      (case coe v19 of
                                                         C_no'45'builtin_6
                                                           -> case coe v19 of
                                                                C_no'45'builtin_6
                                                                  -> let v20
                                                                           = coe
                                                                               MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                               erased in
                                                                     coe
                                                                       (case coe v20 of
                                                                          C_step_630 v22 v23
                                                                            -> coe
                                                                                 C_step_630
                                                                                 (coe
                                                                                    MAlonzo.Code.Untyped.C_case_40
                                                                                    (coe v22)
                                                                                    (coe v2))
                                                                                 (coe
                                                                                    C_case'45'reduce_458
                                                                                    v23)
                                                                          C_done_634 v22
                                                                            -> case coe v22 of
                                                                                 C_unsat'8321'_218 v25 v27 v28
                                                                                   -> coe
                                                                                        C_step_630
                                                                                        (coe
                                                                                           MAlonzo.Code.Untyped.C_error_46)
                                                                                        (coe
                                                                                           C_case'45'unsat'8321'_450
                                                                                           v25)
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                C_want_8 v20 v21
                                                                  -> case coe v20 of
                                                                       0 -> case coe v21 of
                                                                              0 -> let v22
                                                                                         = coe
                                                                                             MAlonzo.Code.Untyped.C__'183'__22
                                                                                             (coe
                                                                                                d_reduceBuiltin_248
                                                                                                (0 ::
                                                                                                   Integer)
                                                                                                v3)
                                                                                             (coe
                                                                                                v4) in
                                                                                   coe
                                                                                     (let v23
                                                                                            = coe
                                                                                                C_ξ'8321'_258
                                                                                                (coe
                                                                                                   C_sat'45'app'45'builtin_298) in
                                                                                      coe
                                                                                        (coe
                                                                                           C_step_630
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C_case_40
                                                                                              (coe
                                                                                                 v22)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_case'45'reduce_458
                                                                                              v23)))
                                                                              1 -> let v22
                                                                                         = coe
                                                                                             d_reduceBuiltin_248
                                                                                             (0 ::
                                                                                                Integer)
                                                                                             v1 in
                                                                                   coe
                                                                                     (let v23
                                                                                            = coe
                                                                                                C_sat'45'app'45'builtin_298 in
                                                                                      coe
                                                                                        (coe
                                                                                           C_step_630
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C_case_40
                                                                                              (coe
                                                                                                 v22)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_case'45'reduce_458
                                                                                              v23)))
                                                                              _ -> let v22
                                                                                         = subInt
                                                                                             (coe
                                                                                                v21)
                                                                                             (coe
                                                                                                (2 ::
                                                                                                   Integer)) in
                                                                                   coe
                                                                                     (coe
                                                                                        C_step_630
                                                                                        (coe
                                                                                           MAlonzo.Code.Untyped.C_error_46)
                                                                                        (coe
                                                                                           C_case'45'unsat'8321'_450
                                                                                           v22))
                                                                       _ -> let v22
                                                                                  = subInt
                                                                                      (coe v20)
                                                                                      (coe
                                                                                         (1 ::
                                                                                            Integer)) in
                                                                            coe
                                                                              (let v23
                                                                                     = coe
                                                                                         MAlonzo.Code.Untyped.C_error_46 in
                                                                               coe
                                                                                 (let v24
                                                                                        = coe
                                                                                            C_app'45'interleave'45'error_384
                                                                                            v22
                                                                                            v21 in
                                                                                  coe
                                                                                    (coe
                                                                                       C_step_630
                                                                                       (coe
                                                                                          MAlonzo.Code.Untyped.C_case_40
                                                                                          (coe v23)
                                                                                          (coe v2))
                                                                                       (coe
                                                                                          C_case'45'reduce_458
                                                                                          v24))))
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         C_want_8 v20 v21
                                                           -> case coe v20 of
                                                                0 -> case coe v21 of
                                                                       0 -> let v22
                                                                                  = 0 :: Integer in
                                                                            coe
                                                                              (let v23
                                                                                     = 0 ::
                                                                                         Integer in
                                                                               coe
                                                                                 (case coe v22 of
                                                                                    0 -> case coe
                                                                                                v23 of
                                                                                           0 -> let v24
                                                                                                      = coe
                                                                                                          MAlonzo.Code.Untyped.C__'183'__22
                                                                                                          (coe
                                                                                                             d_reduceBuiltin_248
                                                                                                             (0 ::
                                                                                                                Integer)
                                                                                                             v3)
                                                                                                          (coe
                                                                                                             v4) in
                                                                                                coe
                                                                                                  (let v25
                                                                                                         = coe
                                                                                                             C_ξ'8321'_258
                                                                                                             (coe
                                                                                                                C_sat'45'app'45'builtin_298) in
                                                                                                   coe
                                                                                                     (coe
                                                                                                        C_step_630
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Untyped.C_case_40
                                                                                                           (coe
                                                                                                              v24)
                                                                                                           (coe
                                                                                                              v2))
                                                                                                        (coe
                                                                                                           C_case'45'reduce_458
                                                                                                           v25)))
                                                                                           1 -> let v24
                                                                                                      = coe
                                                                                                          d_reduceBuiltin_248
                                                                                                          (1 ::
                                                                                                             Integer)
                                                                                                          v1 in
                                                                                                coe
                                                                                                  (let v25
                                                                                                         = coe
                                                                                                             C_sat'45'app'45'builtin_298 in
                                                                                                   coe
                                                                                                     (coe
                                                                                                        C_step_630
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Untyped.C_case_40
                                                                                                           (coe
                                                                                                              v24)
                                                                                                           (coe
                                                                                                              v2))
                                                                                                        (coe
                                                                                                           C_case'45'reduce_458
                                                                                                           v25)))
                                                                                           _ -> let v24
                                                                                                      = -2 ::
                                                                                                          Integer in
                                                                                                coe
                                                                                                  (coe
                                                                                                     C_step_630
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Untyped.C_error_46)
                                                                                                     (coe
                                                                                                        C_case'45'unsat'8321'_450
                                                                                                        v24))
                                                                                    _ -> let v24
                                                                                               = -1 ::
                                                                                                   Integer in
                                                                                         coe
                                                                                           (let v25
                                                                                                  = coe
                                                                                                      MAlonzo.Code.Untyped.C_error_46 in
                                                                                            coe
                                                                                              (let v26
                                                                                                     = coe
                                                                                                         C_app'45'interleave'45'error_384
                                                                                                         v24
                                                                                                         v23 in
                                                                                               coe
                                                                                                 (coe
                                                                                                    C_step_630
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Untyped.C_case_40
                                                                                                       (coe
                                                                                                          v25)
                                                                                                       (coe
                                                                                                          v2))
                                                                                                    (coe
                                                                                                       C_case'45'reduce_458
                                                                                                       v26))))))
                                                                       _ -> let v22
                                                                                  = subInt
                                                                                      (coe v21)
                                                                                      (coe
                                                                                         (1 ::
                                                                                            Integer)) in
                                                                            coe
                                                                              (let v23
                                                                                     = 0 ::
                                                                                         Integer in
                                                                               coe
                                                                                 (case coe v23 of
                                                                                    0 -> case coe
                                                                                                v21 of
                                                                                           1 -> let v24
                                                                                                      = coe
                                                                                                          MAlonzo.Code.Untyped.C__'183'__22
                                                                                                          (coe
                                                                                                             d_reduceBuiltin_248
                                                                                                             (0 ::
                                                                                                                Integer)
                                                                                                             v3)
                                                                                                          (coe
                                                                                                             v4) in
                                                                                                coe
                                                                                                  (let v25
                                                                                                         = coe
                                                                                                             C_ξ'8321'_258
                                                                                                             (coe
                                                                                                                C_sat'45'app'45'builtin_298) in
                                                                                                   coe
                                                                                                     (coe
                                                                                                        C_step_630
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Untyped.C_case_40
                                                                                                           (coe
                                                                                                              v24)
                                                                                                           (coe
                                                                                                              v2))
                                                                                                        (coe
                                                                                                           C_case'45'reduce_458
                                                                                                           v25)))
                                                                                           2 -> let v24
                                                                                                      = coe
                                                                                                          d_reduceBuiltin_248
                                                                                                          (0 ::
                                                                                                             Integer)
                                                                                                          v1 in
                                                                                                coe
                                                                                                  (let v25
                                                                                                         = coe
                                                                                                             C_sat'45'app'45'builtin_298 in
                                                                                                   coe
                                                                                                     (coe
                                                                                                        C_step_630
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Untyped.C_case_40
                                                                                                           (coe
                                                                                                              v24)
                                                                                                           (coe
                                                                                                              v2))
                                                                                                        (coe
                                                                                                           C_case'45'reduce_458
                                                                                                           v25)))
                                                                                           _ -> let v24
                                                                                                      = subInt
                                                                                                          (coe
                                                                                                             v21)
                                                                                                          (coe
                                                                                                             (3 ::
                                                                                                                Integer)) in
                                                                                                coe
                                                                                                  (coe
                                                                                                     C_step_630
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Untyped.C_error_46)
                                                                                                     (coe
                                                                                                        C_case'45'unsat'8321'_450
                                                                                                        v24))
                                                                                    _ -> let v24
                                                                                               = -1 ::
                                                                                                   Integer in
                                                                                         coe
                                                                                           (let v25
                                                                                                  = coe
                                                                                                      MAlonzo.Code.Untyped.C_error_46 in
                                                                                            coe
                                                                                              (let v26
                                                                                                     = coe
                                                                                                         C_app'45'interleave'45'error_384
                                                                                                         v24
                                                                                                         v22 in
                                                                                               coe
                                                                                                 (coe
                                                                                                    C_step_630
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Untyped.C_case_40
                                                                                                       (coe
                                                                                                          v25)
                                                                                                       (coe
                                                                                                          v2))
                                                                                                    (coe
                                                                                                       C_case'45'reduce_458
                                                                                                       v26))))))
                                                                _ -> let v22
                                                                           = coe
                                                                               d_interleave'45'error_32
                                                                               erased in
                                                                     coe
                                                                       (case coe v22 of
                                                                          C_no'45'builtin_6
                                                                            -> let v23
                                                                                     = coe
                                                                                         MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                         erased in
                                                                               coe
                                                                                 (case coe v23 of
                                                                                    C_step_630 v25 v26
                                                                                      -> coe
                                                                                           C_step_630
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C_case_40
                                                                                              (coe
                                                                                                 v25)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_case'45'reduce_458
                                                                                              v26)
                                                                                    C_done_634 v25
                                                                                      -> case coe
                                                                                                v25 of
                                                                                           C_unsat'8321'_218 v28 v30 v31
                                                                                             -> coe
                                                                                                  C_step_630
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Untyped.C_error_46)
                                                                                                  (coe
                                                                                                     C_case'45'unsat'8321'_450
                                                                                                     v28)
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          C_want_8 v23 v24
                                                                            -> case coe v23 of
                                                                                 0 -> case coe
                                                                                             v24 of
                                                                                        0 -> let v25
                                                                                                   = coe
                                                                                                       MAlonzo.Code.Untyped.C__'183'__22
                                                                                                       (coe
                                                                                                          d_reduceBuiltin_248
                                                                                                          (0 ::
                                                                                                             Integer)
                                                                                                          v3)
                                                                                                       (coe
                                                                                                          v4) in
                                                                                             coe
                                                                                               (let v26
                                                                                                      = coe
                                                                                                          C_ξ'8321'_258
                                                                                                          (coe
                                                                                                             C_sat'45'app'45'builtin_298) in
                                                                                                coe
                                                                                                  (coe
                                                                                                     C_step_630
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Untyped.C_case_40
                                                                                                        (coe
                                                                                                           v25)
                                                                                                        (coe
                                                                                                           v2))
                                                                                                     (coe
                                                                                                        C_case'45'reduce_458
                                                                                                        v26)))
                                                                                        1 -> let v25
                                                                                                   = coe
                                                                                                       d_reduceBuiltin_248
                                                                                                       (0 ::
                                                                                                          Integer)
                                                                                                       v1 in
                                                                                             coe
                                                                                               (let v26
                                                                                                      = coe
                                                                                                          C_sat'45'app'45'builtin_298 in
                                                                                                coe
                                                                                                  (coe
                                                                                                     C_step_630
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Untyped.C_case_40
                                                                                                        (coe
                                                                                                           v25)
                                                                                                        (coe
                                                                                                           v2))
                                                                                                     (coe
                                                                                                        C_case'45'reduce_458
                                                                                                        v26)))
                                                                                        _ -> let v25
                                                                                                   = subInt
                                                                                                       (coe
                                                                                                          v24)
                                                                                                       (coe
                                                                                                          (2 ::
                                                                                                             Integer)) in
                                                                                             coe
                                                                                               (coe
                                                                                                  C_step_630
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Untyped.C_error_46)
                                                                                                  (coe
                                                                                                     C_case'45'unsat'8321'_450
                                                                                                     v25))
                                                                                 _ -> let v25
                                                                                            = subInt
                                                                                                (coe
                                                                                                   v23)
                                                                                                (coe
                                                                                                   (1 ::
                                                                                                      Integer)) in
                                                                                      coe
                                                                                        (let v26
                                                                                               = coe
                                                                                                   MAlonzo.Code.Untyped.C_error_46 in
                                                                                         coe
                                                                                           (let v27
                                                                                                  = coe
                                                                                                      C_app'45'interleave'45'error_384
                                                                                                      v25
                                                                                                      v24 in
                                                                                            coe
                                                                                              (coe
                                                                                                 C_step_630
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Untyped.C_case_40
                                                                                                    (coe
                                                                                                       v26)
                                                                                                    (coe
                                                                                                       v2))
                                                                                                 (coe
                                                                                                    C_case'45'reduce_458
                                                                                                    v27))))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        C_constr_224 v13
                                          -> let v14 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v15 = coe C_app'45'constr_404 in
                                                coe
                                                  (coe
                                                     C_step_630
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v14)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_458 v15)))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_fail_636
                                   -> let v9 = coe MAlonzo.Code.Untyped.C_error_46 in
                                      coe
                                        (let v10 = coe C_error'8322'_290 in
                                         coe
                                           (coe
                                              C_step_630
                                              (coe MAlonzo.Code.Untyped.C_case_40 (coe v9) (coe v2))
                                              (coe C_case'45'reduce_458 v10)))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_fail_636
                         -> let v6 = coe MAlonzo.Code.Untyped.C_error_46 in
                            coe
                              (let v7 = coe C_error'8321'_286 in
                               coe
                                 (coe
                                    C_step_630
                                    (coe MAlonzo.Code.Untyped.C_case_40 (coe v6) (coe v2))
                                    (coe C_case'45'reduce_458 v7)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_force_24 v3
               -> let v4 = d_progress_640 (coe v3) in
                  coe
                    (case coe v4 of
                       C_step_630 v6 v7
                         -> let v8 = coe MAlonzo.Code.Untyped.C_force_24 (coe v6) in
                            coe
                              (let v9 = coe C_ξ'8323'_272 v7 in
                               coe
                                 (coe
                                    C_step_630
                                    (coe MAlonzo.Code.Untyped.C_case_40 (coe v8) (coe v2))
                                    (coe C_case'45'reduce_458 v9)))
                       C_done_634 v6
                         -> let v7 = coe du_sat_36 (coe v3) in
                            coe
                              (case coe v7 of
                                 C_no'45'builtin_6
                                   -> case coe v3 of
                                        MAlonzo.Code.Untyped.C_ƛ_20 v8
                                          -> let v9 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v10 = coe C_force'45'ƛ_358 in
                                                coe
                                                  (coe
                                                     C_step_630
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v9)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_458 v10)))
                                        MAlonzo.Code.Untyped.C__'183'__22 v8 v9
                                          -> let v10
                                                   = seq
                                                       (coe v6)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                          erased) in
                                             coe
                                               (case coe v10 of
                                                  C_step_630 v12 v13
                                                    -> coe
                                                         C_step_630
                                                         (coe
                                                            MAlonzo.Code.Untyped.C_case_40 (coe v12)
                                                            (coe v2))
                                                         (coe C_case'45'reduce_458 v13)
                                                  C_done_634 v12
                                                    -> case coe v12 of
                                                         C_unsat'8320'_204 v14 v15 v17
                                                           -> coe
                                                                C_step_630
                                                                (coe
                                                                   MAlonzo.Code.Untyped.C_error_46)
                                                                (coe
                                                                   C_case'45'unsat'8320'_442 v14
                                                                   v15)
                                                         C_unsat'8320''8331''8321'_210 v14 v16
                                                           -> coe
                                                                C_step_630
                                                                (coe
                                                                   MAlonzo.Code.Untyped.C_error_46)
                                                                (coe C_case'45'unsat'8321'_450 v14)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        MAlonzo.Code.Untyped.C_force_24 v8
                                          -> let v9
                                                   = seq
                                                       (coe v6)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                          erased) in
                                             coe
                                               (case coe v9 of
                                                  C_step_630 v11 v12
                                                    -> coe
                                                         C_step_630
                                                         (coe
                                                            MAlonzo.Code.Untyped.C_case_40 (coe v11)
                                                            (coe v2))
                                                         (coe C_case'45'reduce_458 v12)
                                                  C_done_634 v11
                                                    -> case coe v11 of
                                                         C_unsat'8320'_204 v13 v14 v16
                                                           -> coe
                                                                C_step_630
                                                                (coe
                                                                   MAlonzo.Code.Untyped.C_error_46)
                                                                (coe
                                                                   C_case'45'unsat'8320'_442 v13
                                                                   v14)
                                                         C_unsat'8320''8331''8321'_210 v13 v15
                                                           -> coe
                                                                C_step_630
                                                                (coe
                                                                   MAlonzo.Code.Untyped.C_error_46)
                                                                (coe C_case'45'unsat'8321'_450 v13)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        MAlonzo.Code.Untyped.C_delay_26 v8
                                          -> let v9 = coe C_force'45'delay_282 in
                                             coe
                                               (coe
                                                  C_step_630
                                                  (coe
                                                     MAlonzo.Code.Untyped.C_case_40 (coe v8)
                                                     (coe v2))
                                                  (coe C_case'45'reduce_458 v9))
                                        MAlonzo.Code.Untyped.C_con_28 v8
                                          -> let v9 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v10 = coe C_force'45'con_362 in
                                                coe
                                                  (coe
                                                     C_step_630
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v9)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_458 v10)))
                                        MAlonzo.Code.Untyped.C_constr_34 v8 v9
                                          -> let v10 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v11 = coe C_force'45'constr_368 in
                                                coe
                                                  (coe
                                                     C_step_630
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v10)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_458 v11)))
                                        MAlonzo.Code.Untyped.C_error_46
                                          -> let v8 = coe C_force'45'error_292 in
                                             coe
                                               (coe
                                                  C_step_630
                                                  (coe
                                                     MAlonzo.Code.Untyped.C_case_40 (coe v3)
                                                     (coe v2))
                                                  (coe C_case'45'reduce_458 v8))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_want_8 v8 v9
                                   -> case coe v8 of
                                        0 -> let v10 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v11
                                                      = coe C_force'45'interleave'45'error_374 v9 in
                                                coe
                                                  (coe
                                                     C_step_630
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v10)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_458 v11)))
                                        1 -> case coe v9 of
                                               0 -> let v10
                                                          = coe
                                                              d_reduceBuiltin_248 (0 :: Integer)
                                                              v1 in
                                                    coe
                                                      (let v11
                                                             = coe C_sat'45'force'45'builtin_302 in
                                                       coe
                                                         (coe
                                                            C_step_630
                                                            (coe
                                                               MAlonzo.Code.Untyped.C_case_40
                                                               (coe v10) (coe v2))
                                                            (coe C_case'45'reduce_458 v11)))
                                               _ -> let v10
                                                          = subInt (coe v9) (coe (1 :: Integer)) in
                                                    coe
                                                      (coe
                                                         C_step_630
                                                         (coe MAlonzo.Code.Untyped.C_error_46)
                                                         (coe C_case'45'unsat'8321'_450 v10))
                                        _ -> let v10 = subInt (coe v8) (coe (2 :: Integer)) in
                                             coe
                                               (coe
                                                  C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                                                  (coe C_case'45'unsat'8320'_442 v10 v9))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_fail_636
                         -> let v5 = coe MAlonzo.Code.Untyped.C_error_46 in
                            coe
                              (let v6 = coe C_force'45'error_292 in
                               coe
                                 (coe
                                    C_step_630
                                    (coe MAlonzo.Code.Untyped.C_case_40 (coe v5) (coe v2))
                                    (coe C_case'45'reduce_458 v6)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_delay_26 v3
               -> coe
                    C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                    (coe C_case'45'delay_420)
             MAlonzo.Code.Untyped.C_con_28 v3
               -> coe
                    C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                    (coe C_case'45'con_426)
             MAlonzo.Code.Untyped.C_constr_34 v3 v4
               -> let v5
                        = coe
                            MAlonzo.Code.Untyped.CEK.du_lookup'63'_1004 (coe v3) (coe v2) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                         -> coe
                              C_step_630 (coe du_iterApp_238 (coe v6) (coe v4))
                              (coe C_case'45'constr_312 v6)
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                              (coe C_broken'45'const_320)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_case_40 v3 v4
               -> let v5 = d_progress_640 (coe v1) in
                  coe
                    (case coe v5 of
                       C_step_630 v7 v8
                         -> coe
                              C_step_630 (coe MAlonzo.Code.Untyped.C_case_40 (coe v7) (coe v2))
                              (coe C_case'45'reduce_458 v8)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_builtin_44 v3
               -> coe
                    C_step_630 (coe MAlonzo.Code.Untyped.C_error_46)
                    (coe C_case'45'builtin_432)
             MAlonzo.Code.Untyped.C_error_46
               -> coe C_step_630 v1 (coe C_case'45'error_408)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.C_builtin_44 v1
        -> coe C_done_634 (coe C_builtin_196)
      MAlonzo.Code.Untyped.C_error_46 -> coe C_fail_636
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Reduction._≅_
d__'8773'__1308 a0 a1 = ()
data T__'8773'__1308
  = C_reduce_1316 MAlonzo.Code.Untyped.T__'8866'_14
                  T__'10230''42'__460 T__'10230''42'__460
-- Untyped.Reduction.refl-≅
d_refl'45''8773'_1320 ::
  MAlonzo.Code.Untyped.T__'8866'_14 -> T__'8773'__1308
d_refl'45''8773'_1320 v0
  = coe C_reduce_1316 v0 (coe C_refl_464) (coe C_refl_464)
-- Untyped.Reduction.integer
d_integer_1322 :: MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4
d_integer_1322
  = coe
      MAlonzo.Code.RawU.du_tag2TyTag_232
      (coe MAlonzo.Code.RawU.C_integer_30)
-- Untyped.Reduction.con-integer
d_con'45'integer_1326 ::
  Integer -> Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_con'45'integer_1326 ~v0 v1 = du_con'45'integer_1326 v1
du_con'45'integer_1326 ::
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14
du_con'45'integer_1326 v0
  = coe
      MAlonzo.Code.Untyped.C_con_28
      (coe MAlonzo.Code.RawU.C_tmCon_206 (coe d_integer_1322) (coe v0))
-- Untyped.Reduction.ex1
d_ex1_1338 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ex1_1338
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C__'183'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C__'183'__22
               (coe
                  MAlonzo.Code.Untyped.C_ƛ_20
                  (coe
                     MAlonzo.Code.Untyped.C__'183'__22
                     (coe
                        MAlonzo.Code.Untyped.C_'96'_18
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe
                        MAlonzo.Code.Untyped.C_'96'_18
                        (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
               (coe
                  MAlonzo.Code.Untyped.C_'96'_18
                  (coe
                     MAlonzo.Code.Data.Fin.Base.C_suc_16
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
         (coe du_con'45'integer_1326 (coe (2 :: Integer))))
      (coe du_con'45'integer_1326 (coe (3 :: Integer)))
-- Untyped.Reduction.ex2
d_ex2_1340 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ex2_1340
  = coe
      MAlonzo.Code.Untyped.C__'183'__22
      (coe
         MAlonzo.Code.Untyped.C__'183'__22
         (coe
            MAlonzo.Code.Untyped.C_ƛ_20
            (coe
               MAlonzo.Code.Untyped.C_ƛ_20
               (coe
                  MAlonzo.Code.Untyped.C__'183'__22
                  (coe
                     MAlonzo.Code.Untyped.C__'183'__22
                     (coe
                        MAlonzo.Code.Untyped.C_'96'_18
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe
                              MAlonzo.Code.Data.Fin.Base.C_suc_16
                              (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                     (coe
                        MAlonzo.Code.Untyped.C_'96'_18
                        (coe
                           MAlonzo.Code.Data.Fin.Base.C_suc_16
                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))))
                  (coe
                     MAlonzo.Code.Untyped.C_'96'_18
                     (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
         (coe du_con'45'integer_1326 (coe (3 :: Integer))))
      (coe du_con'45'integer_1326 (coe (2 :: Integer)))
