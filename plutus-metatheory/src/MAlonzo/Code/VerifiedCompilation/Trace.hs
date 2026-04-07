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

module MAlonzo.Code.VerifiedCompilation.Trace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Utils

import UntypedPlutusCore.Transform.Simplifier
import UntypedPlutusCore.Transform.Certify.Trace
import qualified UntypedPlutusCore.Transform.Certify.Hints as Hints
import FFI.CostInfo
-- VerifiedCompilation.Trace.SimplifierTag
d_SimplifierTag_4 = ()
type T_SimplifierTag_4 = SimplifierStage
pattern C_floatDelayT_6 = FloatDelay
pattern C_forceDelayT_8 = ForceDelay
pattern C_forceCaseDelayT_10 = ForceCaseDelay
pattern C_caseOfCaseT_12 = CaseOfCase
pattern C_caseReduceT_14 = CaseReduce
pattern C_inlineT_16 = Inline
pattern C_cseT_18 = CSE
pattern C_applyToCaseT_20 = ApplyToCase
pattern C_letFloatOutT_22 = LetFloatOut
pattern C_unknown_24 = Unknown
check_floatDelayT_6 :: T_SimplifierTag_4
check_floatDelayT_6 = FloatDelay
check_forceDelayT_8 :: T_SimplifierTag_4
check_forceDelayT_8 = ForceDelay
check_forceCaseDelayT_10 :: T_SimplifierTag_4
check_forceCaseDelayT_10 = ForceCaseDelay
check_caseOfCaseT_12 :: T_SimplifierTag_4
check_caseOfCaseT_12 = CaseOfCase
check_caseReduceT_14 :: T_SimplifierTag_4
check_caseReduceT_14 = CaseReduce
check_inlineT_16 :: T_SimplifierTag_4
check_inlineT_16 = Inline
check_cseT_18 :: T_SimplifierTag_4
check_cseT_18 = CSE
check_applyToCaseT_20 :: T_SimplifierTag_4
check_applyToCaseT_20 = ApplyToCase
check_letFloatOutT_22 :: T_SimplifierTag_4
check_letFloatOutT_22 = LetFloatOut
check_unknown_24 :: T_SimplifierTag_4
check_unknown_24 = Unknown
cover_SimplifierTag_4 :: SimplifierStage -> ()
cover_SimplifierTag_4 x
  = case x of
      FloatDelay -> ()
      ForceDelay -> ()
      ForceCaseDelay -> ()
      CaseOfCase -> ()
      CaseReduce -> ()
      Inline -> ()
      CSE -> ()
      ApplyToCase -> ()
      LetFloatOut -> ()
      Unknown -> ()
-- VerifiedCompilation.Trace.InlineHints
d_InlineHints_26 = ()
type T_InlineHints_26 = Hints.Inline
pattern C_var_28 = Hints.InlVar
pattern C_expand_30 a0 = Hints.InlExpand a0
pattern C_ƛ_32 a0 = Hints.InlLam a0
pattern C_ƛ'8595'_34 a0 = Hints.InlLamDrop a0
pattern C__'183'__36 a0 a1 = Hints.InlApply a0 a1
pattern C__'183''8595'_38 a0 = Hints.InlDrop a0
pattern C_force_40 a0 = Hints.InlForce a0
pattern C_delay_42 a0 = Hints.InlDelay a0
pattern C_con_44 = Hints.InlCon
pattern C_builtin_46 = Hints.InlBuiltin
pattern C_error_48 = Hints.InlError
pattern C_constr_50 a0 = Hints.InlConstr a0
pattern C_case_52 a0 a1 = Hints.InlCase a0 a1
check_var_28 :: T_InlineHints_26
check_var_28 = Hints.InlVar
check_expand_30 :: T_InlineHints_26 -> T_InlineHints_26
check_expand_30 = Hints.InlExpand
check_ƛ_32 :: T_InlineHints_26 -> T_InlineHints_26
check_ƛ_32 = Hints.InlLam
check_ƛ'8595'_34 :: T_InlineHints_26 -> T_InlineHints_26
check_ƛ'8595'_34 = Hints.InlLamDrop
check__'183'__36 ::
  T_InlineHints_26 -> T_InlineHints_26 -> T_InlineHints_26
check__'183'__36 = Hints.InlApply
check__'183''8595'_38 :: T_InlineHints_26 -> T_InlineHints_26
check__'183''8595'_38 = Hints.InlDrop
check_force_40 :: T_InlineHints_26 -> T_InlineHints_26
check_force_40 = Hints.InlForce
check_delay_42 :: T_InlineHints_26 -> T_InlineHints_26
check_delay_42 = Hints.InlDelay
check_con_44 :: T_InlineHints_26
check_con_44 = Hints.InlCon
check_builtin_46 :: T_InlineHints_26
check_builtin_46 = Hints.InlBuiltin
check_error_48 :: T_InlineHints_26
check_error_48 = Hints.InlError
check_constr_50 ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_26 ->
  T_InlineHints_26
check_constr_50 = Hints.InlConstr
check_case_52 ::
  T_InlineHints_26 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_26 ->
  T_InlineHints_26
check_case_52 = Hints.InlCase
cover_InlineHints_26 :: Hints.Inline -> ()
cover_InlineHints_26 x
  = case x of
      Hints.InlVar -> ()
      Hints.InlExpand _ -> ()
      Hints.InlLam _ -> ()
      Hints.InlLamDrop _ -> ()
      Hints.InlApply _ _ -> ()
      Hints.InlDrop _ -> ()
      Hints.InlForce _ -> ()
      Hints.InlDelay _ -> ()
      Hints.InlCon -> ()
      Hints.InlBuiltin -> ()
      Hints.InlError -> ()
      Hints.InlConstr _ -> ()
      Hints.InlCase _ _ -> ()
-- VerifiedCompilation.Trace.Hints
d_Hints_54 = ()
type T_Hints_54 = Hints.Hints
pattern C_inline_56 a0 = Hints.Inline a0
pattern C_none_58 = Hints.NoHints
check_inline_56 :: T_InlineHints_26 -> T_Hints_54
check_inline_56 = Hints.Inline
check_none_58 :: T_Hints_54
check_none_58 = Hints.NoHints
cover_Hints_54 :: Hints.Hints -> ()
cover_Hints_54 x
  = case x of
      Hints.Inline _ -> ()
      Hints.NoHints -> ()
-- VerifiedCompilation.Trace.Trace
d_Trace_62 a0 = ()
data T_Trace_62
  = C_step_66 T_SimplifierTag_4 T_Hints_54 AgdaAny T_Trace_62 |
    C_done_68 AgdaAny
-- VerifiedCompilation.Trace.head
d_head_72 :: T_Trace_62 -> AgdaAny
d_head_72 v0
  = case coe v0 of
      C_step_66 v1 v2 v3 v4 -> coe v3
      C_done_68 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace.Dump
d_Dump_78 :: ()
d_Dump_78 = erased
-- VerifiedCompilation.Trace.toTrace
d_toTrace_80 ::
  [MAlonzo.Code.Utils.T__'215'__428
     T_SimplifierTag_4
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_54
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  Maybe T_Trace_62
d_toTrace_80 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_go_90 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace._.go
d_go_90 ::
  MAlonzo.Code.Utils.T__'215'__428
    T_SimplifierTag_4
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_54
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     T_SimplifierTag_4
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_54
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  MAlonzo.Code.Utils.T__'215'__428
    T_SimplifierTag_4
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_54
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     T_SimplifierTag_4
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_54
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  T_Trace_62
d_go_90 ~v0 ~v1 v2 v3 = du_go_90 v2 v3
du_go_90 ::
  MAlonzo.Code.Utils.T__'215'__428
    T_SimplifierTag_4
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_54
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     T_SimplifierTag_4
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_54
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  T_Trace_62
du_go_90 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__442 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Utils.C__'44'__442 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Utils.C__'44'__442 v6 v7
                      -> case coe v1 of
                           []
                             -> coe
                                  C_step_66 (coe v2) (coe v4) (coe v6) (coe C_done_68 (coe v7))
                           (:) v8 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Utils.C__'44'__442 v10 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Utils.C__'44'__442 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Utils.C__'44'__442 v14 v15
                                                  -> coe
                                                       C_step_66 (coe v2) (coe v4) (coe v6)
                                                       (coe
                                                          du_go_90
                                                          (coe
                                                             MAlonzo.Code.Utils.C__'44'__442
                                                             (coe v10)
                                                             (coe
                                                                MAlonzo.Code.Utils.C__'44'__442
                                                                (coe v12)
                                                                (coe
                                                                   MAlonzo.Code.Utils.C__'44'__442
                                                                   (coe v7) (coe v15))))
                                                          (coe v9))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace.EvalResult
d_EvalResult_116 = ()
type T_EvalResult_116 = EvalResult
pattern C_success_118 a0 a1 = EvalSuccess a0 a1
pattern C_failure_120 a0 a1 a2 = EvalFailure a0 a1 a2
check_success_118 :: Integer -> Integer -> T_EvalResult_116
check_success_118 = EvalSuccess
check_failure_120 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Integer -> T_EvalResult_116
check_failure_120 = EvalFailure
cover_EvalResult_116 :: EvalResult -> ()
cover_EvalResult_116 x
  = case x of
      EvalSuccess _ _ -> ()
      EvalFailure _ _ _ -> ()
