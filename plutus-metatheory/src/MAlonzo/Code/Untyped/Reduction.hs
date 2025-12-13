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
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Signature
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
d_sat_36 :: () -> MAlonzo.Code.Untyped.T__'8866'_14 -> T_Arity_4
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
             C_want_8 (coe MAlonzo.Code.Builtin.d_arity'8320'_304 (coe v1))
             (coe MAlonzo.Code.Builtin.d_arity_308 (coe v1))
      MAlonzo.Code.Untyped.C_error_46 -> coe C_no'45'builtin_6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Reduction.sat-app-step
d_sat'45'app'45'step_114 ::
  () ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sat'45'app'45'step_114 = erased
-- Untyped.Reduction.sat-force-step
d_sat'45'force'45'step_138 ::
  () ->
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
d_Value_182 a0 a1 = ()
data T_Value_182
  = C_delay_188 | C_ƛ_192 | C_con_196 | C_builtin_200 |
    C_unsat'8320'_208 Integer Integer T_Value_182 |
    C_unsat'8320''8331''8321'_214 Integer T_Value_182 |
    C_unsat'8321'_222 Integer T_Value_182 T_Value_182 |
    C_constr_228 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- Untyped.Reduction.value-constr-recurse
d_value'45'constr'45'recurse_234 ::
  () ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  T_Value_182 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_value'45'constr'45'recurse_234 ~v0 ~v1 ~v2 v3
  = du_value'45'constr'45'recurse_234 v3
du_value'45'constr'45'recurse_234 ::
  T_Value_182 -> MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_value'45'constr'45'recurse_234 v0
  = case coe v0 of
      C_constr_228 v3
        -> case coe v3 of
             MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50 -> coe v3
             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
               -> coe
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v6 v7
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Reduction.iterApp
d_iterApp_242 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_iterApp_242 ~v0 v1 v2 = du_iterApp_242 v1 v2
du_iterApp_242 ::
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Untyped.T__'8866'_14
du_iterApp_242 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe
             du_iterApp_242
             (coe MAlonzo.Code.Untyped.C__'183'__22 (coe v0) (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Reduction.reduceBuiltin
d_reduceBuiltin_252
  = error
      "MAlonzo Runtime Error: postulate evaluated: Untyped.Reduction.reduceBuiltin"
-- Untyped.Reduction._⟶_
d__'10230'__256 a0 a1 a2 = ()
data T__'10230'__256
  = C_ξ'8321'_266 T__'10230'__256 |
    C_ξ'8322'_274 T_Value_182 T__'10230'__256 |
    C_ξ'8323'_280 T__'10230'__256 | C_β_286 T_Value_182 |
    C_force'45'delay_290 | C_error'8321'_294 | C_error'8322'_298 |
    C_force'45'error_300 | C_sat'45'app'45'builtin_306 |
    C_sat'45'force'45'builtin_310 |
    C_case'45'constr_320 MAlonzo.Code.Untyped.T__'8866'_14 |
    C_broken'45'const_328 | C_constr'45'step_338 T__'10230'__256 |
    C_constr'45'sub'45'step_348 T__'10230'__256 |
    C_constr'45'error_354 |
    C_constr'45'sub'45'error_362 T__'10230'__256 | C_force'45'ƛ_366 |
    C_force'45'con_370 | C_force'45'constr_376 |
    C_force'45'interleave'45'error_382 Integer |
    C_app'45'interleave'45'error_392 Integer Integer |
    C_app'45'con_398 | C_app'45'delay_404 | C_app'45'constr_412 |
    C_case'45'error_416 | C_case'45'ƛ_422 | C_case'45'delay_428 |
    C_case'45'con_434 | C_case'45'builtin_440 |
    C_case'45'unsat'8320'_450 Integer Integer |
    C_case'45'unsat'8321'_458 Integer |
    C_case'45'reduce_466 T__'10230'__256
-- Untyped.Reduction._⟶*_
d__'10230''42'__470 a0 a1 a2 = ()
data T__'10230''42'__470
  = C_refl_476 |
    C_trans_484 MAlonzo.Code.Untyped.T__'8866'_14 T__'10230'__256
                T__'10230''42'__470
-- Untyped.Reduction.tran-⟶*
d_tran'45''10230''42'_494 ::
  () ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  T__'10230''42'__470 -> T__'10230''42'__470 -> T__'10230''42'__470
d_tran'45''10230''42'_494 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_tran'45''10230''42'_494 v4 v5
du_tran'45''10230''42'_494 ::
  T__'10230''42'__470 -> T__'10230''42'__470 -> T__'10230''42'__470
du_tran'45''10230''42'_494 v0 v1
  = case coe v0 of
      C_refl_476 -> coe v1
      C_trans_484 v3 v5 v6
        -> case coe v1 of
             C_refl_476 -> coe C_trans_484 v3 v5 v6
             C_trans_484 v8 v10 v11
               -> coe
                    C_trans_484 v3 v5
                    (coe
                       du_tran'45''10230''42'_494 (coe v6) (coe C_trans_484 v8 v10 v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Reduction.Progress
d_Progress_514 a0 a1 = ()
data T_Progress_514
  = C_step_522 MAlonzo.Code.Untyped.T__'8866'_14 T__'10230'__256 |
    C_done_526 T_Value_182 | C_fail_528
-- Untyped.Reduction.progress
d_progress_532 ::
  MAlonzo.Code.Untyped.T__'8866'_14 -> T_Progress_514
d_progress_532 v0
  = case coe v0 of
      MAlonzo.Code.Untyped.C_ƛ_20 v1 -> coe C_done_526 (coe C_ƛ_192)
      MAlonzo.Code.Untyped.C__'183'__22 v1 v2
        -> let v3 = d_progress_532 (coe v1) in
           coe
             (case coe v3 of
                C_step_522 v5 v6
                  -> coe
                       C_step_522
                       (coe MAlonzo.Code.Untyped.C__'183'__22 (coe v5) (coe v2))
                       (coe C_ξ'8321'_266 v6)
                C_done_526 v5
                  -> let v6 = d_progress_532 (coe v2) in
                     coe
                       (case coe v6 of
                          C_step_522 v8 v9
                            -> coe
                                 C_step_522
                                 (coe MAlonzo.Code.Untyped.C__'183'__22 (coe v1) (coe v8))
                                 (coe C_ξ'8322'_274 v5 v9)
                          C_done_526 v8
                            -> case coe v5 of
                                 C_delay_188
                                   -> coe
                                        C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_app'45'delay_404)
                                 C_ƛ_192
                                   -> case coe v1 of
                                        MAlonzo.Code.Untyped.C_ƛ_20 v10
                                          -> coe
                                               C_step_522
                                               (coe
                                                  MAlonzo.Code.Untyped.RenamingSubstitution.du__'91'_'93'_468
                                                  (coe v10) (coe v2))
                                               (coe C_β_286 v8)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_con_196
                                   -> coe
                                        C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_app'45'con_398)
                                 C_builtin_200
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
                                                                MAlonzo.Code.Builtin.Signature.d_args_86
                                                                (coe
                                                                   MAlonzo.Code.Builtin.d_signature_302
                                                                   (coe v10))))) in
                                             coe
                                               (let v12
                                                      = addInt
                                                          (coe
                                                             MAlonzo.Code.Builtin.Signature.d_fv'9839'_84
                                                             (coe
                                                                MAlonzo.Code.Builtin.d_signature_302
                                                                (coe v10)))
                                                          (coe
                                                             MAlonzo.Code.Builtin.Signature.d_fv'8902'_82
                                                             (coe
                                                                MAlonzo.Code.Builtin.d_signature_302
                                                                (coe v10))) in
                                                coe
                                                  (case coe v12 of
                                                     0 -> case coe v11 of
                                                            1 -> coe
                                                                   C_step_522
                                                                   (coe
                                                                      d_reduceBuiltin_252 erased v0)
                                                                   (coe C_sat'45'app'45'builtin_306)
                                                            _ -> let v13
                                                                       = subInt
                                                                           (coe v11)
                                                                           (coe (2 :: Integer)) in
                                                                 coe
                                                                   (coe
                                                                      C_done_526
                                                                      (coe
                                                                         C_unsat'8321'_222 v13 v5
                                                                         v8))
                                                     _ -> let v13
                                                                = subInt
                                                                    (coe v12)
                                                                    (coe (1 :: Integer)) in
                                                          coe
                                                            (coe
                                                               C_step_522
                                                               (coe MAlonzo.Code.Untyped.C_error_46)
                                                               (coe
                                                                  C_app'45'interleave'45'error_392
                                                                  v13 v11))))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_unsat'8320'_208 v10 v11 v13
                                   -> coe
                                        C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_app'45'interleave'45'error_392 v10 v11)
                                 C_unsat'8320''8331''8321'_214 v10 v12
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
                                                                              C_step_522
                                                                              (coe
                                                                                 MAlonzo.Code.Untyped.C__'183'__22
                                                                                 (coe
                                                                                    d_reduceBuiltin_252
                                                                                    erased v1)
                                                                                 (coe v2))
                                                                              (coe
                                                                                 C_ξ'8321'_266
                                                                                 (coe
                                                                                    C_sat'45'force'45'builtin_310))
                                                                       1 -> coe
                                                                              C_step_522
                                                                              (coe
                                                                                 d_reduceBuiltin_252
                                                                                 erased v0)
                                                                              (coe
                                                                                 C_sat'45'app'45'builtin_306)
                                                                       _ -> let v17
                                                                                  = subInt
                                                                                      (coe v16)
                                                                                      (coe
                                                                                         (2 ::
                                                                                            Integer)) in
                                                                            coe
                                                                              (coe
                                                                                 C_done_526
                                                                                 (coe
                                                                                    C_unsat'8321'_222
                                                                                    v17 v5 v8))
                                                                _ -> let v17
                                                                           = subInt
                                                                               (coe v15)
                                                                               (coe
                                                                                  (1 :: Integer)) in
                                                                     coe
                                                                       (coe
                                                                          C_step_522
                                                                          (coe
                                                                             MAlonzo.Code.Untyped.C_error_46)
                                                                          (coe
                                                                             C_app'45'interleave'45'error_392
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
                                                                                        C_step_522
                                                                                        (coe
                                                                                           MAlonzo.Code.Untyped.C__'183'__22
                                                                                           (coe
                                                                                              d_reduceBuiltin_252
                                                                                              erased
                                                                                              v1)
                                                                                           (coe v2))
                                                                                        (coe
                                                                                           C_ξ'8321'_266
                                                                                           (coe
                                                                                              C_sat'45'force'45'builtin_310))
                                                                                 1 -> coe
                                                                                        C_step_522
                                                                                        (coe
                                                                                           d_reduceBuiltin_252
                                                                                           erased
                                                                                           v0)
                                                                                        (coe
                                                                                           C_sat'45'app'45'builtin_306)
                                                                                 _ -> let v20
                                                                                            = subInt
                                                                                                (coe
                                                                                                   v19)
                                                                                                (coe
                                                                                                   (2 ::
                                                                                                      Integer)) in
                                                                                      coe
                                                                                        (coe
                                                                                           C_done_526
                                                                                           (coe
                                                                                              C_unsat'8321'_222
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
                                                                                    C_step_522
                                                                                    (coe
                                                                                       MAlonzo.Code.Untyped.C_error_46)
                                                                                    (coe
                                                                                       C_app'45'interleave'45'error_392
                                                                                       v20 v19))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         1 -> case coe v16 of
                                                                0 -> coe
                                                                       C_step_522
                                                                       (coe
                                                                          MAlonzo.Code.Untyped.C__'183'__22
                                                                          (coe
                                                                             d_reduceBuiltin_252
                                                                             erased v1)
                                                                          (coe v2))
                                                                       (coe
                                                                          C_ξ'8321'_266
                                                                          (coe
                                                                             C_sat'45'force'45'builtin_310))
                                                                1 -> coe
                                                                       C_step_522
                                                                       (coe
                                                                          d_reduceBuiltin_252 erased
                                                                          v0)
                                                                       (coe
                                                                          C_sat'45'app'45'builtin_306)
                                                                _ -> let v17
                                                                           = subInt
                                                                               (coe v16)
                                                                               (coe
                                                                                  (2 :: Integer)) in
                                                                     coe
                                                                       (coe
                                                                          C_done_526
                                                                          (coe
                                                                             C_unsat'8321'_222 v17
                                                                             v5 v8))
                                                         _ -> let v17
                                                                    = subInt
                                                                        (coe v15)
                                                                        (coe (2 :: Integer)) in
                                                              coe
                                                                (coe
                                                                   C_step_522
                                                                   (coe
                                                                      MAlonzo.Code.Untyped.C_error_46)
                                                                   (coe
                                                                      C_app'45'interleave'45'error_392
                                                                      v17 v16))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_unsat'8321'_222 v11 v13 v14
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
                                                                              C_step_522
                                                                              (coe
                                                                                 MAlonzo.Code.Untyped.C__'183'__22
                                                                                 (coe
                                                                                    d_reduceBuiltin_252
                                                                                    erased v1)
                                                                                 (coe v2))
                                                                              (coe
                                                                                 C_ξ'8321'_266
                                                                                 (coe
                                                                                    C_sat'45'app'45'builtin_306))
                                                                       1 -> coe
                                                                              C_step_522
                                                                              (coe
                                                                                 d_reduceBuiltin_252
                                                                                 erased v0)
                                                                              (coe
                                                                                 C_sat'45'app'45'builtin_306)
                                                                       _ -> let v20
                                                                                  = subInt
                                                                                      (coe v19)
                                                                                      (coe
                                                                                         (2 ::
                                                                                            Integer)) in
                                                                            coe
                                                                              (coe
                                                                                 C_done_526
                                                                                 (coe
                                                                                    C_unsat'8321'_222
                                                                                    v20 v5 v8))
                                                                _ -> let v20
                                                                           = subInt
                                                                               (coe v18)
                                                                               (coe
                                                                                  (1 :: Integer)) in
                                                                     coe
                                                                       (coe
                                                                          C_step_522
                                                                          (coe
                                                                             MAlonzo.Code.Untyped.C_error_46)
                                                                          (coe
                                                                             C_app'45'interleave'45'error_392
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
                                                                                           C_step_522
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C__'183'__22
                                                                                              (coe
                                                                                                 d_reduceBuiltin_252
                                                                                                 erased
                                                                                                 v1)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_ξ'8321'_266
                                                                                              (coe
                                                                                                 C_sat'45'app'45'builtin_306))
                                                                                    1 -> coe
                                                                                           C_step_522
                                                                                           (coe
                                                                                              d_reduceBuiltin_252
                                                                                              erased
                                                                                              v0)
                                                                                           (coe
                                                                                              C_sat'45'app'45'builtin_306)
                                                                                    _ -> let v22
                                                                                               = -2 ::
                                                                                                   Integer in
                                                                                         coe
                                                                                           (coe
                                                                                              C_done_526
                                                                                              (coe
                                                                                                 C_unsat'8321'_222
                                                                                                 v22
                                                                                                 v5
                                                                                                 v8))
                                                                             _ -> let v22
                                                                                        = -1 ::
                                                                                            Integer in
                                                                                  coe
                                                                                    (coe
                                                                                       C_step_522
                                                                                       (coe
                                                                                          MAlonzo.Code.Untyped.C_error_46)
                                                                                       (coe
                                                                                          C_app'45'interleave'45'error_392
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
                                                                                           C_step_522
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C__'183'__22
                                                                                              (coe
                                                                                                 d_reduceBuiltin_252
                                                                                                 erased
                                                                                                 v1)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_ξ'8321'_266
                                                                                              (coe
                                                                                                 C_sat'45'app'45'builtin_306))
                                                                                    2 -> coe
                                                                                           C_step_522
                                                                                           (coe
                                                                                              d_reduceBuiltin_252
                                                                                              erased
                                                                                              v0)
                                                                                           (coe
                                                                                              C_sat'45'app'45'builtin_306)
                                                                                    _ -> let v22
                                                                                               = subInt
                                                                                                   (coe
                                                                                                      v19)
                                                                                                   (coe
                                                                                                      (3 ::
                                                                                                         Integer)) in
                                                                                         coe
                                                                                           (coe
                                                                                              C_done_526
                                                                                              (coe
                                                                                                 C_unsat'8321'_222
                                                                                                 v22
                                                                                                 v5
                                                                                                 v8))
                                                                             _ -> let v22
                                                                                        = -1 ::
                                                                                            Integer in
                                                                                  coe
                                                                                    (coe
                                                                                       C_step_522
                                                                                       (coe
                                                                                          MAlonzo.Code.Untyped.C_error_46)
                                                                                       (coe
                                                                                          C_app'45'interleave'45'error_392
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
                                                                                        C_step_522
                                                                                        (coe
                                                                                           MAlonzo.Code.Untyped.C__'183'__22
                                                                                           (coe
                                                                                              d_reduceBuiltin_252
                                                                                              erased
                                                                                              v1)
                                                                                           (coe v2))
                                                                                        (coe
                                                                                           C_ξ'8321'_266
                                                                                           (coe
                                                                                              C_sat'45'app'45'builtin_306))
                                                                                 1 -> coe
                                                                                        C_step_522
                                                                                        (coe
                                                                                           d_reduceBuiltin_252
                                                                                           erased
                                                                                           v0)
                                                                                        (coe
                                                                                           C_sat'45'app'45'builtin_306)
                                                                                 _ -> let v23
                                                                                            = subInt
                                                                                                (coe
                                                                                                   v22)
                                                                                                (coe
                                                                                                   (2 ::
                                                                                                      Integer)) in
                                                                                      coe
                                                                                        (coe
                                                                                           C_done_526
                                                                                           (coe
                                                                                              C_unsat'8321'_222
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
                                                                                    C_step_522
                                                                                    (coe
                                                                                       MAlonzo.Code.Untyped.C_error_46)
                                                                                    (coe
                                                                                       C_app'45'interleave'45'error_392
                                                                                       v23 v22))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_constr_228 v11
                                   -> coe
                                        C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_app'45'constr_412)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          C_fail_528
                            -> coe
                                 C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                                 (coe C_error'8322'_298)
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_fail_528
                  -> coe
                       C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                       (coe C_error'8321'_294)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Untyped.C_force_24 v1
        -> let v2 = d_progress_532 (coe v1) in
           coe
             (case coe v2 of
                C_step_522 v4 v5
                  -> coe
                       C_step_522 (coe MAlonzo.Code.Untyped.C_force_24 (coe v4))
                       (coe C_ξ'8323'_280 v5)
                C_done_526 v4
                  -> let v5 = coe du_sat_36 (coe v1) in
                     coe
                       (case coe v5 of
                          C_no'45'builtin_6
                            -> case coe v1 of
                                 MAlonzo.Code.Untyped.C_ƛ_20 v6
                                   -> coe
                                        C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_force'45'ƛ_366)
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
                                   -> coe C_step_522 v6 (coe C_force'45'delay_290)
                                 MAlonzo.Code.Untyped.C_con_28 v6
                                   -> coe
                                        C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_force'45'con_370)
                                 MAlonzo.Code.Untyped.C_constr_34 v6 v7
                                   -> coe
                                        C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_force'45'constr_376)
                                 MAlonzo.Code.Untyped.C_error_46
                                   -> coe C_step_522 v1 (coe C_force'45'error_300)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          C_want_8 v6 v7
                            -> case coe v6 of
                                 0 -> coe
                                        C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                                        (coe C_force'45'interleave'45'error_382 v7)
                                 1 -> case coe v7 of
                                        0 -> coe
                                               C_step_522 (coe d_reduceBuiltin_252 erased v0)
                                               (coe C_sat'45'force'45'builtin_310)
                                        _ -> let v8 = subInt (coe v7) (coe (1 :: Integer)) in
                                             coe
                                               (coe
                                                  C_done_526
                                                  (coe C_unsat'8320''8331''8321'_214 v8 v4))
                                 _ -> let v8 = subInt (coe v6) (coe (2 :: Integer)) in
                                      coe (coe C_done_526 (coe C_unsat'8320'_208 v8 v7 v4))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                C_fail_528
                  -> coe
                       C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                       (coe C_force'45'error_300)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Untyped.C_delay_26 v1
        -> coe C_done_526 (coe C_delay_188)
      MAlonzo.Code.Untyped.C_con_28 v1 -> coe C_done_526 (coe C_con_196)
      MAlonzo.Code.Untyped.C_constr_34 v1 v2
        -> case coe v2 of
             []
               -> coe
                    C_done_526
                    (coe
                       C_constr_228
                       (coe MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))
             (:) v3 v4
               -> let v5 = d_progress_532 (coe v3) in
                  coe
                    (case coe v5 of
                       C_step_522 v7 v8
                         -> coe
                              C_step_522
                              (coe
                                 MAlonzo.Code.Untyped.C_constr_34 (coe v1)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7) (coe v4)))
                              (coe C_constr'45'step_338 v8)
                       C_done_526 v7
                         -> let v8
                                  = d_progress_532
                                      (coe MAlonzo.Code.Untyped.C_constr_34 (coe v1) (coe v4)) in
                            coe
                              (case coe v8 of
                                 C_step_522 v10 v11
                                   -> case coe v11 of
                                        C_constr'45'step_338 v16
                                          -> case coe v4 of
                                               (:) v17 v18
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Untyped.C_constr_34 v19 v20
                                                        -> case coe v20 of
                                                             (:) v21 v22
                                                               -> coe
                                                                    C_step_522
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
                                                                       C_constr'45'sub'45'step_348
                                                                       (coe
                                                                          C_constr'45'step_338 v16))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        C_constr'45'sub'45'step_348 v16
                                          -> case coe v4 of
                                               (:) v17 v18
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Untyped.C_constr_34 v19 v20
                                                        -> case coe v20 of
                                                             (:) v21 v22
                                                               -> coe
                                                                    C_step_522
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
                                                                       C_constr'45'sub'45'step_348
                                                                       (coe
                                                                          C_constr'45'sub'45'step_348
                                                                          v16))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        C_constr'45'error_354
                                          -> coe
                                               C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                                               (coe
                                                  C_constr'45'sub'45'error_362
                                                  (coe C_constr'45'error_354))
                                        C_constr'45'sub'45'error_362 v15
                                          -> coe
                                               C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                                               (coe
                                                  C_constr'45'sub'45'error_362
                                                  (coe C_constr'45'sub'45'error_362 v15))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_done_526 v10
                                   -> coe
                                        C_done_526
                                        (coe
                                           C_constr_228
                                           (coe
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                              v7 (coe du_value'45'constr'45'recurse_234 (coe v10))))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_fail_528
                         -> coe
                              C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                              (coe C_constr'45'error_354)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.C_case_40 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Untyped.C_ƛ_20 v3
               -> coe
                    C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                    (coe C_case'45'ƛ_422)
             MAlonzo.Code.Untyped.C__'183'__22 v3 v4
               -> let v5 = d_progress_532 (coe v3) in
                  coe
                    (case coe v5 of
                       C_step_522 v7 v8
                         -> let v9
                                  = coe MAlonzo.Code.Untyped.C__'183'__22 (coe v7) (coe v4) in
                            coe
                              (let v10 = coe C_ξ'8321'_266 v8 in
                               coe
                                 (coe
                                    C_step_522
                                    (coe MAlonzo.Code.Untyped.C_case_40 (coe v9) (coe v2))
                                    (coe C_case'45'reduce_466 v10)))
                       C_done_526 v7
                         -> let v8 = d_progress_532 (coe v4) in
                            coe
                              (case coe v8 of
                                 C_step_522 v10 v11
                                   -> let v12
                                            = coe
                                                MAlonzo.Code.Untyped.C__'183'__22 (coe v3)
                                                (coe v10) in
                                      coe
                                        (let v13 = coe C_ξ'8322'_274 v7 v11 in
                                         coe
                                           (coe
                                              C_step_522
                                              (coe
                                                 MAlonzo.Code.Untyped.C_case_40 (coe v12) (coe v2))
                                              (coe C_case'45'reduce_466 v13)))
                                 C_done_526 v10
                                   -> case coe v7 of
                                        C_delay_188
                                          -> let v12 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v13 = coe C_app'45'delay_404 in
                                                coe
                                                  (coe
                                                     C_step_522
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v12)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_466 v13)))
                                        C_ƛ_192
                                          -> case coe v3 of
                                               MAlonzo.Code.Untyped.C_ƛ_20 v12
                                                 -> let v13
                                                          = coe
                                                              MAlonzo.Code.Untyped.RenamingSubstitution.du__'91'_'93'_468
                                                              (coe v12) (coe v4) in
                                                    coe
                                                      (let v14 = coe C_β_286 v10 in
                                                       coe
                                                         (coe
                                                            C_step_522
                                                            (coe
                                                               MAlonzo.Code.Untyped.C_case_40
                                                               (coe v13) (coe v2))
                                                            (coe C_case'45'reduce_466 v14)))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        C_con_196
                                          -> let v12 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v13 = coe C_app'45'con_398 in
                                                coe
                                                  (coe
                                                     C_step_522
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v12)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_466 v13)))
                                        C_builtin_200
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
                                                                       MAlonzo.Code.Builtin.Signature.d_args_86
                                                                       (coe
                                                                          MAlonzo.Code.Builtin.d_signature_302
                                                                          (coe v12))))) in
                                                    coe
                                                      (let v14
                                                             = addInt
                                                                 (coe
                                                                    MAlonzo.Code.Builtin.Signature.d_fv'9839'_84
                                                                    (coe
                                                                       MAlonzo.Code.Builtin.d_signature_302
                                                                       (coe v12)))
                                                                 (coe
                                                                    MAlonzo.Code.Builtin.Signature.d_fv'8902'_82
                                                                    (coe
                                                                       MAlonzo.Code.Builtin.d_signature_302
                                                                       (coe v12))) in
                                                       coe
                                                         (case coe v14 of
                                                            0 -> case coe v13 of
                                                                   1 -> let v15
                                                                              = coe
                                                                                  d_reduceBuiltin_252
                                                                                  erased v1 in
                                                                        coe
                                                                          (let v16
                                                                                 = coe
                                                                                     C_sat'45'app'45'builtin_306 in
                                                                           coe
                                                                             (coe
                                                                                C_step_522
                                                                                (coe
                                                                                   MAlonzo.Code.Untyped.C_case_40
                                                                                   (coe v15)
                                                                                   (coe v2))
                                                                                (coe
                                                                                   C_case'45'reduce_466
                                                                                   v16)))
                                                                   _ -> let v15
                                                                              = subInt
                                                                                  (coe v13)
                                                                                  (coe
                                                                                     (2 ::
                                                                                        Integer)) in
                                                                        coe
                                                                          (coe
                                                                             C_step_522
                                                                             (coe
                                                                                MAlonzo.Code.Untyped.C_error_46)
                                                                             (coe
                                                                                C_case'45'unsat'8321'_458
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
                                                                                 C_app'45'interleave'45'error_392
                                                                                 v15 v13 in
                                                                       coe
                                                                         (coe
                                                                            C_step_522
                                                                            (coe
                                                                               MAlonzo.Code.Untyped.C_case_40
                                                                               (coe v16) (coe v2))
                                                                            (coe
                                                                               C_case'45'reduce_466
                                                                               v17))))))
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        C_unsat'8320'_208 v12 v13 v15
                                          -> let v16 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v17
                                                      = coe
                                                          C_app'45'interleave'45'error_392 v12
                                                          v13 in
                                                coe
                                                  (coe
                                                     C_step_522
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v16)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_466 v17)))
                                        C_unsat'8320''8331''8321'_214 v12 v14
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
                                                                          C_step_522 v19 v20
                                                                            -> coe
                                                                                 C_step_522
                                                                                 (coe
                                                                                    MAlonzo.Code.Untyped.C_case_40
                                                                                    (coe v19)
                                                                                    (coe v2))
                                                                                 (coe
                                                                                    C_case'45'reduce_466
                                                                                    v20)
                                                                          C_done_526 v19
                                                                            -> case coe v19 of
                                                                                 C_unsat'8321'_222 v22 v24 v25
                                                                                   -> coe
                                                                                        C_step_522
                                                                                        (coe
                                                                                           MAlonzo.Code.Untyped.C_error_46)
                                                                                        (coe
                                                                                           C_case'45'unsat'8321'_458
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
                                                                                                d_reduceBuiltin_252
                                                                                                erased
                                                                                                v3)
                                                                                             (coe
                                                                                                v4) in
                                                                                   coe
                                                                                     (let v20
                                                                                            = coe
                                                                                                C_ξ'8321'_266
                                                                                                (coe
                                                                                                   C_sat'45'force'45'builtin_310) in
                                                                                      coe
                                                                                        (coe
                                                                                           C_step_522
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C_case_40
                                                                                              (coe
                                                                                                 v19)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_case'45'reduce_466
                                                                                              v20)))
                                                                              1 -> let v19
                                                                                         = coe
                                                                                             d_reduceBuiltin_252
                                                                                             erased
                                                                                             v1 in
                                                                                   coe
                                                                                     (let v20
                                                                                            = coe
                                                                                                C_sat'45'app'45'builtin_306 in
                                                                                      coe
                                                                                        (coe
                                                                                           C_step_522
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C_case_40
                                                                                              (coe
                                                                                                 v19)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_case'45'reduce_466
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
                                                                                        C_step_522
                                                                                        (coe
                                                                                           MAlonzo.Code.Untyped.C_error_46)
                                                                                        (coe
                                                                                           C_case'45'unsat'8321'_458
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
                                                                                            C_app'45'interleave'45'error_392
                                                                                            v19
                                                                                            v18 in
                                                                                  coe
                                                                                    (coe
                                                                                       C_step_522
                                                                                       (coe
                                                                                          MAlonzo.Code.Untyped.C_case_40
                                                                                          (coe v20)
                                                                                          (coe v2))
                                                                                       (coe
                                                                                          C_case'45'reduce_466
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
                                                                                    C_step_522 v22 v23
                                                                                      -> coe
                                                                                           C_step_522
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C_case_40
                                                                                              (coe
                                                                                                 v22)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_case'45'reduce_466
                                                                                              v23)
                                                                                    C_done_526 v22
                                                                                      -> case coe
                                                                                                v22 of
                                                                                           C_unsat'8321'_222 v25 v27 v28
                                                                                             -> coe
                                                                                                  C_step_522
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Untyped.C_error_46)
                                                                                                  (coe
                                                                                                     C_case'45'unsat'8321'_458
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
                                                                                                          d_reduceBuiltin_252
                                                                                                          erased
                                                                                                          v3)
                                                                                                       (coe
                                                                                                          v4) in
                                                                                             coe
                                                                                               (let v23
                                                                                                      = coe
                                                                                                          C_ξ'8321'_266
                                                                                                          (coe
                                                                                                             C_sat'45'force'45'builtin_310) in
                                                                                                coe
                                                                                                  (coe
                                                                                                     C_step_522
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Untyped.C_case_40
                                                                                                        (coe
                                                                                                           v22)
                                                                                                        (coe
                                                                                                           v2))
                                                                                                     (coe
                                                                                                        C_case'45'reduce_466
                                                                                                        v23)))
                                                                                        1 -> let v22
                                                                                                   = coe
                                                                                                       d_reduceBuiltin_252
                                                                                                       erased
                                                                                                       v1 in
                                                                                             coe
                                                                                               (let v23
                                                                                                      = coe
                                                                                                          C_sat'45'app'45'builtin_306 in
                                                                                                coe
                                                                                                  (coe
                                                                                                     C_step_522
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Untyped.C_case_40
                                                                                                        (coe
                                                                                                           v22)
                                                                                                        (coe
                                                                                                           v2))
                                                                                                     (coe
                                                                                                        C_case'45'reduce_466
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
                                                                                                  C_step_522
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Untyped.C_error_46)
                                                                                                  (coe
                                                                                                     C_case'45'unsat'8321'_458
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
                                                                                                      C_app'45'interleave'45'error_392
                                                                                                      v22
                                                                                                      v21 in
                                                                                            coe
                                                                                              (coe
                                                                                                 C_step_522
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Untyped.C_case_40
                                                                                                    (coe
                                                                                                       v23)
                                                                                                    (coe
                                                                                                       v2))
                                                                                                 (coe
                                                                                                    C_case'45'reduce_466
                                                                                                    v24))))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                                1 -> case coe v18 of
                                                                       0 -> let v19
                                                                                  = coe
                                                                                      MAlonzo.Code.Untyped.C__'183'__22
                                                                                      (coe
                                                                                         d_reduceBuiltin_252
                                                                                         erased v3)
                                                                                      (coe v4) in
                                                                            coe
                                                                              (let v20
                                                                                     = coe
                                                                                         C_ξ'8321'_266
                                                                                         (coe
                                                                                            C_sat'45'force'45'builtin_310) in
                                                                               coe
                                                                                 (coe
                                                                                    C_step_522
                                                                                    (coe
                                                                                       MAlonzo.Code.Untyped.C_case_40
                                                                                       (coe v19)
                                                                                       (coe v2))
                                                                                    (coe
                                                                                       C_case'45'reduce_466
                                                                                       v20)))
                                                                       1 -> let v19
                                                                                  = coe
                                                                                      d_reduceBuiltin_252
                                                                                      erased v1 in
                                                                            coe
                                                                              (let v20
                                                                                     = coe
                                                                                         C_sat'45'app'45'builtin_306 in
                                                                               coe
                                                                                 (coe
                                                                                    C_step_522
                                                                                    (coe
                                                                                       MAlonzo.Code.Untyped.C_case_40
                                                                                       (coe v19)
                                                                                       (coe v2))
                                                                                    (coe
                                                                                       C_case'45'reduce_466
                                                                                       v20)))
                                                                       _ -> let v19
                                                                                  = subInt
                                                                                      (coe v18)
                                                                                      (coe
                                                                                         (2 ::
                                                                                            Integer)) in
                                                                            coe
                                                                              (coe
                                                                                 C_step_522
                                                                                 (coe
                                                                                    MAlonzo.Code.Untyped.C_error_46)
                                                                                 (coe
                                                                                    C_case'45'unsat'8321'_458
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
                                                                                     C_app'45'interleave'45'error_392
                                                                                     v19 v18 in
                                                                           coe
                                                                             (coe
                                                                                C_step_522
                                                                                (coe
                                                                                   MAlonzo.Code.Untyped.C_case_40
                                                                                   (coe v20)
                                                                                   (coe v2))
                                                                                (coe
                                                                                   C_case'45'reduce_466
                                                                                   v21))))
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        C_unsat'8321'_222 v13 v15 v16
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
                                                                          C_step_522 v22 v23
                                                                            -> coe
                                                                                 C_step_522
                                                                                 (coe
                                                                                    MAlonzo.Code.Untyped.C_case_40
                                                                                    (coe v22)
                                                                                    (coe v2))
                                                                                 (coe
                                                                                    C_case'45'reduce_466
                                                                                    v23)
                                                                          C_done_526 v22
                                                                            -> case coe v22 of
                                                                                 C_unsat'8321'_222 v25 v27 v28
                                                                                   -> coe
                                                                                        C_step_522
                                                                                        (coe
                                                                                           MAlonzo.Code.Untyped.C_error_46)
                                                                                        (coe
                                                                                           C_case'45'unsat'8321'_458
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
                                                                                                d_reduceBuiltin_252
                                                                                                erased
                                                                                                v3)
                                                                                             (coe
                                                                                                v4) in
                                                                                   coe
                                                                                     (let v23
                                                                                            = coe
                                                                                                C_ξ'8321'_266
                                                                                                (coe
                                                                                                   C_sat'45'app'45'builtin_306) in
                                                                                      coe
                                                                                        (coe
                                                                                           C_step_522
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C_case_40
                                                                                              (coe
                                                                                                 v22)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_case'45'reduce_466
                                                                                              v23)))
                                                                              1 -> let v22
                                                                                         = coe
                                                                                             d_reduceBuiltin_252
                                                                                             erased
                                                                                             v1 in
                                                                                   coe
                                                                                     (let v23
                                                                                            = coe
                                                                                                C_sat'45'app'45'builtin_306 in
                                                                                      coe
                                                                                        (coe
                                                                                           C_step_522
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C_case_40
                                                                                              (coe
                                                                                                 v22)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_case'45'reduce_466
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
                                                                                        C_step_522
                                                                                        (coe
                                                                                           MAlonzo.Code.Untyped.C_error_46)
                                                                                        (coe
                                                                                           C_case'45'unsat'8321'_458
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
                                                                                            C_app'45'interleave'45'error_392
                                                                                            v22
                                                                                            v21 in
                                                                                  coe
                                                                                    (coe
                                                                                       C_step_522
                                                                                       (coe
                                                                                          MAlonzo.Code.Untyped.C_case_40
                                                                                          (coe v23)
                                                                                          (coe v2))
                                                                                       (coe
                                                                                          C_case'45'reduce_466
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
                                                                                                             d_reduceBuiltin_252
                                                                                                             erased
                                                                                                             v3)
                                                                                                          (coe
                                                                                                             v4) in
                                                                                                coe
                                                                                                  (let v25
                                                                                                         = coe
                                                                                                             C_ξ'8321'_266
                                                                                                             (coe
                                                                                                                C_sat'45'app'45'builtin_306) in
                                                                                                   coe
                                                                                                     (coe
                                                                                                        C_step_522
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Untyped.C_case_40
                                                                                                           (coe
                                                                                                              v24)
                                                                                                           (coe
                                                                                                              v2))
                                                                                                        (coe
                                                                                                           C_case'45'reduce_466
                                                                                                           v25)))
                                                                                           1 -> let v24
                                                                                                      = coe
                                                                                                          d_reduceBuiltin_252
                                                                                                          erased
                                                                                                          v1 in
                                                                                                coe
                                                                                                  (let v25
                                                                                                         = coe
                                                                                                             C_sat'45'app'45'builtin_306 in
                                                                                                   coe
                                                                                                     (coe
                                                                                                        C_step_522
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Untyped.C_case_40
                                                                                                           (coe
                                                                                                              v24)
                                                                                                           (coe
                                                                                                              v2))
                                                                                                        (coe
                                                                                                           C_case'45'reduce_466
                                                                                                           v25)))
                                                                                           _ -> let v24
                                                                                                      = -2 ::
                                                                                                          Integer in
                                                                                                coe
                                                                                                  (coe
                                                                                                     C_step_522
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Untyped.C_error_46)
                                                                                                     (coe
                                                                                                        C_case'45'unsat'8321'_458
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
                                                                                                         C_app'45'interleave'45'error_392
                                                                                                         v24
                                                                                                         v23 in
                                                                                               coe
                                                                                                 (coe
                                                                                                    C_step_522
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Untyped.C_case_40
                                                                                                       (coe
                                                                                                          v25)
                                                                                                       (coe
                                                                                                          v2))
                                                                                                    (coe
                                                                                                       C_case'45'reduce_466
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
                                                                                                             d_reduceBuiltin_252
                                                                                                             erased
                                                                                                             v3)
                                                                                                          (coe
                                                                                                             v4) in
                                                                                                coe
                                                                                                  (let v25
                                                                                                         = coe
                                                                                                             C_ξ'8321'_266
                                                                                                             (coe
                                                                                                                C_sat'45'app'45'builtin_306) in
                                                                                                   coe
                                                                                                     (coe
                                                                                                        C_step_522
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Untyped.C_case_40
                                                                                                           (coe
                                                                                                              v24)
                                                                                                           (coe
                                                                                                              v2))
                                                                                                        (coe
                                                                                                           C_case'45'reduce_466
                                                                                                           v25)))
                                                                                           2 -> let v24
                                                                                                      = coe
                                                                                                          d_reduceBuiltin_252
                                                                                                          erased
                                                                                                          v1 in
                                                                                                coe
                                                                                                  (let v25
                                                                                                         = coe
                                                                                                             C_sat'45'app'45'builtin_306 in
                                                                                                   coe
                                                                                                     (coe
                                                                                                        C_step_522
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Untyped.C_case_40
                                                                                                           (coe
                                                                                                              v24)
                                                                                                           (coe
                                                                                                              v2))
                                                                                                        (coe
                                                                                                           C_case'45'reduce_466
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
                                                                                                     C_step_522
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Untyped.C_error_46)
                                                                                                     (coe
                                                                                                        C_case'45'unsat'8321'_458
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
                                                                                                         C_app'45'interleave'45'error_392
                                                                                                         v24
                                                                                                         v22 in
                                                                                               coe
                                                                                                 (coe
                                                                                                    C_step_522
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Untyped.C_case_40
                                                                                                       (coe
                                                                                                          v25)
                                                                                                       (coe
                                                                                                          v2))
                                                                                                    (coe
                                                                                                       C_case'45'reduce_466
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
                                                                                    C_step_522 v25 v26
                                                                                      -> coe
                                                                                           C_step_522
                                                                                           (coe
                                                                                              MAlonzo.Code.Untyped.C_case_40
                                                                                              (coe
                                                                                                 v25)
                                                                                              (coe
                                                                                                 v2))
                                                                                           (coe
                                                                                              C_case'45'reduce_466
                                                                                              v26)
                                                                                    C_done_526 v25
                                                                                      -> case coe
                                                                                                v25 of
                                                                                           C_unsat'8321'_222 v28 v30 v31
                                                                                             -> coe
                                                                                                  C_step_522
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Untyped.C_error_46)
                                                                                                  (coe
                                                                                                     C_case'45'unsat'8321'_458
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
                                                                                                          d_reduceBuiltin_252
                                                                                                          erased
                                                                                                          v3)
                                                                                                       (coe
                                                                                                          v4) in
                                                                                             coe
                                                                                               (let v26
                                                                                                      = coe
                                                                                                          C_ξ'8321'_266
                                                                                                          (coe
                                                                                                             C_sat'45'app'45'builtin_306) in
                                                                                                coe
                                                                                                  (coe
                                                                                                     C_step_522
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Untyped.C_case_40
                                                                                                        (coe
                                                                                                           v25)
                                                                                                        (coe
                                                                                                           v2))
                                                                                                     (coe
                                                                                                        C_case'45'reduce_466
                                                                                                        v26)))
                                                                                        1 -> let v25
                                                                                                   = coe
                                                                                                       d_reduceBuiltin_252
                                                                                                       erased
                                                                                                       v1 in
                                                                                             coe
                                                                                               (let v26
                                                                                                      = coe
                                                                                                          C_sat'45'app'45'builtin_306 in
                                                                                                coe
                                                                                                  (coe
                                                                                                     C_step_522
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Untyped.C_case_40
                                                                                                        (coe
                                                                                                           v25)
                                                                                                        (coe
                                                                                                           v2))
                                                                                                     (coe
                                                                                                        C_case'45'reduce_466
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
                                                                                                  C_step_522
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Untyped.C_error_46)
                                                                                                  (coe
                                                                                                     C_case'45'unsat'8321'_458
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
                                                                                                      C_app'45'interleave'45'error_392
                                                                                                      v25
                                                                                                      v24 in
                                                                                            coe
                                                                                              (coe
                                                                                                 C_step_522
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Untyped.C_case_40
                                                                                                    (coe
                                                                                                       v26)
                                                                                                    (coe
                                                                                                       v2))
                                                                                                 (coe
                                                                                                    C_case'45'reduce_466
                                                                                                    v27))))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        C_constr_228 v13
                                          -> let v14 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v15 = coe C_app'45'constr_412 in
                                                coe
                                                  (coe
                                                     C_step_522
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v14)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_466 v15)))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_fail_528
                                   -> let v9 = coe MAlonzo.Code.Untyped.C_error_46 in
                                      coe
                                        (let v10 = coe C_error'8322'_298 in
                                         coe
                                           (coe
                                              C_step_522
                                              (coe MAlonzo.Code.Untyped.C_case_40 (coe v9) (coe v2))
                                              (coe C_case'45'reduce_466 v10)))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_fail_528
                         -> let v6 = coe MAlonzo.Code.Untyped.C_error_46 in
                            coe
                              (let v7 = coe C_error'8321'_294 in
                               coe
                                 (coe
                                    C_step_522
                                    (coe MAlonzo.Code.Untyped.C_case_40 (coe v6) (coe v2))
                                    (coe C_case'45'reduce_466 v7)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_force_24 v3
               -> let v4 = d_progress_532 (coe v3) in
                  coe
                    (case coe v4 of
                       C_step_522 v6 v7
                         -> let v8 = coe MAlonzo.Code.Untyped.C_force_24 (coe v6) in
                            coe
                              (let v9 = coe C_ξ'8323'_280 v7 in
                               coe
                                 (coe
                                    C_step_522
                                    (coe MAlonzo.Code.Untyped.C_case_40 (coe v8) (coe v2))
                                    (coe C_case'45'reduce_466 v9)))
                       C_done_526 v6
                         -> let v7 = coe du_sat_36 (coe v3) in
                            coe
                              (case coe v7 of
                                 C_no'45'builtin_6
                                   -> case coe v3 of
                                        MAlonzo.Code.Untyped.C_ƛ_20 v8
                                          -> let v9 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v10 = coe C_force'45'ƛ_366 in
                                                coe
                                                  (coe
                                                     C_step_522
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v9)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_466 v10)))
                                        MAlonzo.Code.Untyped.C__'183'__22 v8 v9
                                          -> let v10
                                                   = seq
                                                       (coe v6)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                          erased) in
                                             coe
                                               (case coe v10 of
                                                  C_step_522 v12 v13
                                                    -> coe
                                                         C_step_522
                                                         (coe
                                                            MAlonzo.Code.Untyped.C_case_40 (coe v12)
                                                            (coe v2))
                                                         (coe C_case'45'reduce_466 v13)
                                                  C_done_526 v12
                                                    -> case coe v12 of
                                                         C_unsat'8320'_208 v14 v15 v17
                                                           -> coe
                                                                C_step_522
                                                                (coe
                                                                   MAlonzo.Code.Untyped.C_error_46)
                                                                (coe
                                                                   C_case'45'unsat'8320'_450 v14
                                                                   v15)
                                                         C_unsat'8320''8331''8321'_214 v14 v16
                                                           -> coe
                                                                C_step_522
                                                                (coe
                                                                   MAlonzo.Code.Untyped.C_error_46)
                                                                (coe C_case'45'unsat'8321'_458 v14)
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
                                                  C_step_522 v11 v12
                                                    -> coe
                                                         C_step_522
                                                         (coe
                                                            MAlonzo.Code.Untyped.C_case_40 (coe v11)
                                                            (coe v2))
                                                         (coe C_case'45'reduce_466 v12)
                                                  C_done_526 v11
                                                    -> case coe v11 of
                                                         C_unsat'8320'_208 v13 v14 v16
                                                           -> coe
                                                                C_step_522
                                                                (coe
                                                                   MAlonzo.Code.Untyped.C_error_46)
                                                                (coe
                                                                   C_case'45'unsat'8320'_450 v13
                                                                   v14)
                                                         C_unsat'8320''8331''8321'_214 v13 v15
                                                           -> coe
                                                                C_step_522
                                                                (coe
                                                                   MAlonzo.Code.Untyped.C_error_46)
                                                                (coe C_case'45'unsat'8321'_458 v13)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        MAlonzo.Code.Untyped.C_delay_26 v8
                                          -> let v9 = coe C_force'45'delay_290 in
                                             coe
                                               (coe
                                                  C_step_522
                                                  (coe
                                                     MAlonzo.Code.Untyped.C_case_40 (coe v8)
                                                     (coe v2))
                                                  (coe C_case'45'reduce_466 v9))
                                        MAlonzo.Code.Untyped.C_con_28 v8
                                          -> let v9 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v10 = coe C_force'45'con_370 in
                                                coe
                                                  (coe
                                                     C_step_522
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v9)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_466 v10)))
                                        MAlonzo.Code.Untyped.C_constr_34 v8 v9
                                          -> let v10 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v11 = coe C_force'45'constr_376 in
                                                coe
                                                  (coe
                                                     C_step_522
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v10)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_466 v11)))
                                        MAlonzo.Code.Untyped.C_error_46
                                          -> let v8 = coe C_force'45'error_300 in
                                             coe
                                               (coe
                                                  C_step_522
                                                  (coe
                                                     MAlonzo.Code.Untyped.C_case_40 (coe v3)
                                                     (coe v2))
                                                  (coe C_case'45'reduce_466 v8))
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 C_want_8 v8 v9
                                   -> case coe v8 of
                                        0 -> let v10 = coe MAlonzo.Code.Untyped.C_error_46 in
                                             coe
                                               (let v11
                                                      = coe C_force'45'interleave'45'error_382 v9 in
                                                coe
                                                  (coe
                                                     C_step_522
                                                     (coe
                                                        MAlonzo.Code.Untyped.C_case_40 (coe v10)
                                                        (coe v2))
                                                     (coe C_case'45'reduce_466 v11)))
                                        1 -> case coe v9 of
                                               0 -> let v10 = coe d_reduceBuiltin_252 erased v1 in
                                                    coe
                                                      (let v11
                                                             = coe C_sat'45'force'45'builtin_310 in
                                                       coe
                                                         (coe
                                                            C_step_522
                                                            (coe
                                                               MAlonzo.Code.Untyped.C_case_40
                                                               (coe v10) (coe v2))
                                                            (coe C_case'45'reduce_466 v11)))
                                               _ -> let v10
                                                          = subInt (coe v9) (coe (1 :: Integer)) in
                                                    coe
                                                      (coe
                                                         C_step_522
                                                         (coe MAlonzo.Code.Untyped.C_error_46)
                                                         (coe C_case'45'unsat'8321'_458 v10))
                                        _ -> let v10 = subInt (coe v8) (coe (2 :: Integer)) in
                                             coe
                                               (coe
                                                  C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                                                  (coe C_case'45'unsat'8320'_450 v10 v9))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       C_fail_528
                         -> let v5 = coe MAlonzo.Code.Untyped.C_error_46 in
                            coe
                              (let v6 = coe C_force'45'error_300 in
                               coe
                                 (coe
                                    C_step_522
                                    (coe MAlonzo.Code.Untyped.C_case_40 (coe v5) (coe v2))
                                    (coe C_case'45'reduce_466 v6)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_delay_26 v3
               -> coe
                    C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                    (coe C_case'45'delay_428)
             MAlonzo.Code.Untyped.C_con_28 v3
               -> coe
                    C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                    (coe C_case'45'con_434)
             MAlonzo.Code.Untyped.C_constr_34 v3 v4
               -> let v5
                        = coe
                            MAlonzo.Code.Untyped.CEK.du_lookup'63'_1000 (coe v3) (coe v2) in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                         -> coe
                              C_step_522 (coe du_iterApp_242 (coe v6) (coe v4))
                              (coe C_case'45'constr_320 v6)
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                              (coe C_broken'45'const_328)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_case_40 v3 v4
               -> let v5 = d_progress_532 (coe v1) in
                  coe
                    (case coe v5 of
                       C_step_522 v7 v8
                         -> coe
                              C_step_522 (coe MAlonzo.Code.Untyped.C_case_40 (coe v7) (coe v2))
                              (coe C_case'45'reduce_466 v8)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Untyped.C_builtin_44 v3
               -> coe
                    C_step_522 (coe MAlonzo.Code.Untyped.C_error_46)
                    (coe C_case'45'builtin_440)
             MAlonzo.Code.Untyped.C_error_46
               -> coe C_step_522 v1 (coe C_case'45'error_416)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Untyped.C_builtin_44 v1
        -> coe C_done_526 (coe C_builtin_200)
      MAlonzo.Code.Untyped.C_error_46 -> coe C_fail_528
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Reduction._≅_
d__'8773'__1202 a0 a1 a2 = ()
data T__'8773'__1202
  = C_reduce_1212 MAlonzo.Code.Untyped.T__'8866'_14
                  T__'10230''42'__470 T__'10230''42'__470
-- Untyped.Reduction.refl-≅
d_refl'45''8773'_1218 ::
  MAlonzo.Code.Untyped.T__'8866'_14 -> T__'8773'__1202
d_refl'45''8773'_1218 v0
  = coe C_reduce_1212 v0 (coe C_refl_476) (coe C_refl_476)
-- Untyped.Reduction.integer
d_integer_1220 :: MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4
d_integer_1220
  = coe
      MAlonzo.Code.RawU.du_tag2TyTag_232
      (coe MAlonzo.Code.RawU.C_integer_30)
-- Untyped.Reduction.con-integer
d_con'45'integer_1224 ::
  () -> Integer -> MAlonzo.Code.Untyped.T__'8866'_14
d_con'45'integer_1224 ~v0 v1 = du_con'45'integer_1224 v1
du_con'45'integer_1224 ::
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14
du_con'45'integer_1224 v0
  = coe
      MAlonzo.Code.Untyped.C_con_28
      (coe MAlonzo.Code.RawU.C_tmCon_206 (coe d_integer_1220) (coe v0))
-- Untyped.Reduction.ex1
d_ex1_1236 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ex1_1236
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
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))))
                     (coe
                        MAlonzo.Code.Untyped.C_'96'_18
                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))))
               (coe
                  MAlonzo.Code.Untyped.C_'96'_18
                  (coe
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))
         (coe du_con'45'integer_1224 (coe (2 :: Integer))))
      (coe du_con'45'integer_1224 (coe (3 :: Integer)))
-- Untyped.Reduction.ex2
d_ex2_1238 :: MAlonzo.Code.Untyped.T__'8866'_14
d_ex2_1238
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
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))))
                     (coe
                        MAlonzo.Code.Untyped.C_'96'_18
                        (coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))))
                  (coe
                     MAlonzo.Code.Untyped.C_'96'_18
                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))))
         (coe du_con'45'integer_1224 (coe (3 :: Integer))))
      (coe du_con'45'integer_1224 (coe (2 :: Integer)))
