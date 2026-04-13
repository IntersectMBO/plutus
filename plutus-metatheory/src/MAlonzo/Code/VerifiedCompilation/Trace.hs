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
pattern C__'183'__34 a0 a1 = Hints.InlApply a0 a1
pattern C__'183''8595'_36 a0 = Hints.InlDrop a0
pattern C_force_38 a0 = Hints.InlForce a0
pattern C_delay_40 a0 = Hints.InlDelay a0
pattern C_con_42 = Hints.InlCon
pattern C_builtin_44 = Hints.InlBuiltin
pattern C_error_46 = Hints.InlError
pattern C_constr_48 a0 = Hints.InlConstr a0
pattern C_case_50 a0 a1 = Hints.InlCase a0 a1
check_var_28 :: T_InlineHints_26
check_var_28 = Hints.InlVar
check_expand_30 :: T_InlineHints_26 -> T_InlineHints_26
check_expand_30 = Hints.InlExpand
check_ƛ_32 :: T_InlineHints_26 -> T_InlineHints_26
check_ƛ_32 = Hints.InlLam
check__'183'__34 ::
  T_InlineHints_26 -> T_InlineHints_26 -> T_InlineHints_26
check__'183'__34 = Hints.InlApply
check__'183''8595'_36 :: T_InlineHints_26 -> T_InlineHints_26
check__'183''8595'_36 = Hints.InlDrop
check_force_38 :: T_InlineHints_26 -> T_InlineHints_26
check_force_38 = Hints.InlForce
check_delay_40 :: T_InlineHints_26 -> T_InlineHints_26
check_delay_40 = Hints.InlDelay
check_con_42 :: T_InlineHints_26
check_con_42 = Hints.InlCon
check_builtin_44 :: T_InlineHints_26
check_builtin_44 = Hints.InlBuiltin
check_error_46 :: T_InlineHints_26
check_error_46 = Hints.InlError
check_constr_48 ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_26 ->
  T_InlineHints_26
check_constr_48 = Hints.InlConstr
check_case_50 ::
  T_InlineHints_26 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_26 ->
  T_InlineHints_26
check_case_50 = Hints.InlCase
cover_InlineHints_26 :: Hints.Inline -> ()
cover_InlineHints_26 x
  = case x of
      Hints.InlVar -> ()
      Hints.InlExpand _ -> ()
      Hints.InlLam _ -> ()
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
d_Hints_52 = ()
type T_Hints_52 = Hints.Hints
pattern C_inline_54 a0 = Hints.Inline a0
pattern C_none_56 = Hints.NoHints
check_inline_54 :: T_InlineHints_26 -> T_Hints_52
check_inline_54 = Hints.Inline
check_none_56 :: T_Hints_52
check_none_56 = Hints.NoHints
cover_Hints_52 :: Hints.Hints -> ()
cover_Hints_52 x
  = case x of
      Hints.Inline _ -> ()
      Hints.NoHints -> ()
-- VerifiedCompilation.Trace.Trace
d_Trace_60 a0 = ()
data T_Trace_60
  = C_step_64 T_SimplifierTag_4 T_Hints_52 AgdaAny T_Trace_60 |
    C_done_66 AgdaAny
-- VerifiedCompilation.Trace.head
d_head_70 :: T_Trace_60 -> AgdaAny
d_head_70 v0
  = case coe v0 of
      C_step_64 v1 v2 v3 v4 -> coe v3
      C_done_66 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace.Dump
d_Dump_76 :: ()
d_Dump_76 = erased
-- VerifiedCompilation.Trace.toTrace
d_toTrace_78 ::
  [MAlonzo.Code.Utils.T__'215'__428
     T_SimplifierTag_4
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_52
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  Maybe T_Trace_60
d_toTrace_78 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_go_88 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace._.go
d_go_88 ::
  MAlonzo.Code.Utils.T__'215'__428
    T_SimplifierTag_4
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_52
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     T_SimplifierTag_4
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_52
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  MAlonzo.Code.Utils.T__'215'__428
    T_SimplifierTag_4
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_52
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     T_SimplifierTag_4
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_52
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  T_Trace_60
d_go_88 ~v0 ~v1 v2 v3 = du_go_88 v2 v3
du_go_88 ::
  MAlonzo.Code.Utils.T__'215'__428
    T_SimplifierTag_4
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_52
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     T_SimplifierTag_4
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_52
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  T_Trace_60
du_go_88 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__442 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Utils.C__'44'__442 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Utils.C__'44'__442 v6 v7
                      -> case coe v1 of
                           []
                             -> coe
                                  C_step_64 (coe v2) (coe v4) (coe v6) (coe C_done_66 (coe v7))
                           (:) v8 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Utils.C__'44'__442 v10 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Utils.C__'44'__442 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Utils.C__'44'__442 v14 v15
                                                  -> coe
                                                       C_step_64 (coe v2) (coe v4) (coe v6)
                                                       (coe
                                                          du_go_88
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
d_EvalResult_114 = ()
type T_EvalResult_114 = EvalResult
pattern C_success_116 a0 a1 = EvalSuccess a0 a1
pattern C_failure_118 a0 a1 a2 = EvalFailure a0 a1 a2
check_success_116 :: Integer -> Integer -> T_EvalResult_114
check_success_116 = EvalSuccess
check_failure_118 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Integer -> T_EvalResult_114
check_failure_118 = EvalFailure
cover_EvalResult_114 :: EvalResult -> ()
cover_EvalResult_114 x
  = case x of
      EvalSuccess _ _ -> ()
      EvalFailure _ _ _ -> ()
