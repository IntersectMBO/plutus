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
-- VerifiedCompilation.Trace.NICSimplifierTag
d_NICSimplifierTag_4 = ()
type T_NICSimplifierTag_4 = NICSimplifierStage
pattern C_caseOfCaseT_6 = CaseOfCase
check_caseOfCaseT_6 :: T_NICSimplifierTag_4
check_caseOfCaseT_6 = CaseOfCase
cover_NICSimplifierTag_4 :: NICSimplifierStage -> ()
cover_NICSimplifierTag_4 x
  = case x of
      CaseOfCase -> ()
-- VerifiedCompilation.Trace.ICSimplifierTag
d_ICSimplifierTag_8 = ()
type T_ICSimplifierTag_8 = ICSimplifierStage
pattern C_floatDelayT_10 = FloatDelay
pattern C_forceDelayT_12 = ForceDelay
pattern C_forceCaseDelayT_14 = ForceCaseDelay
pattern C_caseReduceT_16 = CaseReduce
pattern C_inlineT_18 = Inline
pattern C_cseT_20 = CSE
pattern C_applyToCaseT_22 = ApplyToCase
check_floatDelayT_10 :: T_ICSimplifierTag_8
check_floatDelayT_10 = FloatDelay
check_forceDelayT_12 :: T_ICSimplifierTag_8
check_forceDelayT_12 = ForceDelay
check_forceCaseDelayT_14 :: T_ICSimplifierTag_8
check_forceCaseDelayT_14 = ForceCaseDelay
check_caseReduceT_16 :: T_ICSimplifierTag_8
check_caseReduceT_16 = CaseReduce
check_inlineT_18 :: T_ICSimplifierTag_8
check_inlineT_18 = Inline
check_cseT_20 :: T_ICSimplifierTag_8
check_cseT_20 = CSE
check_applyToCaseT_22 :: T_ICSimplifierTag_8
check_applyToCaseT_22 = ApplyToCase
cover_ICSimplifierTag_8 :: ICSimplifierStage -> ()
cover_ICSimplifierTag_8 x
  = case x of
      FloatDelay -> ()
      ForceDelay -> ()
      ForceCaseDelay -> ()
      CaseReduce -> ()
      Inline -> ()
      CSE -> ()
      ApplyToCase -> ()
-- VerifiedCompilation.Trace.SimplifierTag
d_SimplifierTag_24 :: ()
d_SimplifierTag_24 = erased
-- VerifiedCompilation.Trace.floatDelayTag
d_floatDelayTag_26 ::
  MAlonzo.Code.Utils.T_Either_6
    T_NICSimplifierTag_4 T_ICSimplifierTag_8
d_floatDelayTag_26
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_floatDelayT_10)
-- VerifiedCompilation.Trace.forceDelayTag
d_forceDelayTag_28 ::
  MAlonzo.Code.Utils.T_Either_6
    T_NICSimplifierTag_4 T_ICSimplifierTag_8
d_forceDelayTag_28
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_forceDelayT_12)
-- VerifiedCompilation.Trace.forceCaseDelayTag
d_forceCaseDelayTag_30 ::
  MAlonzo.Code.Utils.T_Either_6
    T_NICSimplifierTag_4 T_ICSimplifierTag_8
d_forceCaseDelayTag_30
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_forceCaseDelayT_14)
-- VerifiedCompilation.Trace.caseReduceTag
d_caseReduceTag_32 ::
  MAlonzo.Code.Utils.T_Either_6
    T_NICSimplifierTag_4 T_ICSimplifierTag_8
d_caseReduceTag_32
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_caseReduceT_16)
-- VerifiedCompilation.Trace.inlineTag
d_inlineTag_34 ::
  MAlonzo.Code.Utils.T_Either_6
    T_NICSimplifierTag_4 T_ICSimplifierTag_8
d_inlineTag_34
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_inlineT_18)
-- VerifiedCompilation.Trace.cseTag
d_cseTag_36 ::
  MAlonzo.Code.Utils.T_Either_6
    T_NICSimplifierTag_4 T_ICSimplifierTag_8
d_cseTag_36 = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_cseT_20)
-- VerifiedCompilation.Trace.applyToCaseTag
d_applyToCaseTag_38 ::
  MAlonzo.Code.Utils.T_Either_6
    T_NICSimplifierTag_4 T_ICSimplifierTag_8
d_applyToCaseTag_38
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_applyToCaseT_22)
-- VerifiedCompilation.Trace.caseOfCaseTag
d_caseOfCaseTag_40 ::
  MAlonzo.Code.Utils.T_Either_6
    T_NICSimplifierTag_4 T_ICSimplifierTag_8
d_caseOfCaseTag_40
  = coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_caseOfCaseT_6)
-- VerifiedCompilation.Trace.InlineHints
d_InlineHints_42 = ()
type T_InlineHints_42 = Hints.Inline
pattern C_var_44 = Hints.InlVar
pattern C_expand_46 a0 = Hints.InlExpand a0
pattern C_ƛ_48 a0 = Hints.InlLam a0
pattern C_ƛ'8595'_50 a0 = Hints.InlLamDrop a0
pattern C__'183'__52 a0 a1 = Hints.InlApply a0 a1
pattern C__'183''8595'_54 a0 = Hints.InlDrop a0
pattern C_force_56 a0 = Hints.InlForce a0
pattern C_delay_58 a0 = Hints.InlDelay a0
pattern C_con_60 = Hints.InlCon
pattern C_builtin_62 = Hints.InlBuiltin
pattern C_error_64 = Hints.InlError
pattern C_constr_66 a0 = Hints.InlConstr a0
pattern C_case_68 a0 a1 = Hints.InlCase a0 a1
check_var_44 :: T_InlineHints_42
check_var_44 = Hints.InlVar
check_expand_46 :: T_InlineHints_42 -> T_InlineHints_42
check_expand_46 = Hints.InlExpand
check_ƛ_48 :: T_InlineHints_42 -> T_InlineHints_42
check_ƛ_48 = Hints.InlLam
check_ƛ'8595'_50 :: T_InlineHints_42 -> T_InlineHints_42
check_ƛ'8595'_50 = Hints.InlLamDrop
check__'183'__52 ::
  T_InlineHints_42 -> T_InlineHints_42 -> T_InlineHints_42
check__'183'__52 = Hints.InlApply
check__'183''8595'_54 :: T_InlineHints_42 -> T_InlineHints_42
check__'183''8595'_54 = Hints.InlDrop
check_force_56 :: T_InlineHints_42 -> T_InlineHints_42
check_force_56 = Hints.InlForce
check_delay_58 :: T_InlineHints_42 -> T_InlineHints_42
check_delay_58 = Hints.InlDelay
check_con_60 :: T_InlineHints_42
check_con_60 = Hints.InlCon
check_builtin_62 :: T_InlineHints_42
check_builtin_62 = Hints.InlBuiltin
check_error_64 :: T_InlineHints_42
check_error_64 = Hints.InlError
check_constr_66 ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_42 ->
  T_InlineHints_42
check_constr_66 = Hints.InlConstr
check_case_68 ::
  T_InlineHints_42 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_42 ->
  T_InlineHints_42
check_case_68 = Hints.InlCase
cover_InlineHints_42 :: Hints.Inline -> ()
cover_InlineHints_42 x
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
d_Hints_70 = ()
type T_Hints_70 = Hints.Hints
pattern C_inline_72 a0 = Hints.Inline a0
pattern C_none_74 = Hints.NoHints
check_inline_72 :: T_InlineHints_42 -> T_Hints_70
check_inline_72 = Hints.Inline
check_none_74 :: T_Hints_70
check_none_74 = Hints.NoHints
cover_Hints_70 :: Hints.Hints -> ()
cover_Hints_70 x
  = case x of
      Hints.Inline _ -> ()
      Hints.NoHints -> ()
-- VerifiedCompilation.Trace.Trace
d_Trace_78 a0 = ()
data T_Trace_78
  = C_step_82 (MAlonzo.Code.Utils.T_Either_6
                 T_NICSimplifierTag_4 T_ICSimplifierTag_8)
              T_Hints_70 AgdaAny T_Trace_78 |
    C_done_84 AgdaAny
-- VerifiedCompilation.Trace.head
d_head_88 :: T_Trace_78 -> AgdaAny
d_head_88 v0
  = case coe v0 of
      C_step_82 v1 v2 v3 v4 -> coe v3
      C_done_84 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace.Dump
d_Dump_94 :: ()
d_Dump_94 = erased
-- VerifiedCompilation.Trace.toTrace
d_toTrace_96 ::
  [MAlonzo.Code.Utils.T__'215'__428
     (MAlonzo.Code.Utils.T_Either_6
        T_NICSimplifierTag_4 T_ICSimplifierTag_8)
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_70
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  Maybe T_Trace_78
d_toTrace_96 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_go_106 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace._.go
d_go_106 ::
  MAlonzo.Code.Utils.T__'215'__428
    (MAlonzo.Code.Utils.T_Either_6
       T_NICSimplifierTag_4 T_ICSimplifierTag_8)
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_70
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     (MAlonzo.Code.Utils.T_Either_6
        T_NICSimplifierTag_4 T_ICSimplifierTag_8)
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_70
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  MAlonzo.Code.Utils.T__'215'__428
    (MAlonzo.Code.Utils.T_Either_6
       T_NICSimplifierTag_4 T_ICSimplifierTag_8)
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_70
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     (MAlonzo.Code.Utils.T_Either_6
        T_NICSimplifierTag_4 T_ICSimplifierTag_8)
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_70
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  T_Trace_78
d_go_106 ~v0 ~v1 v2 v3 = du_go_106 v2 v3
du_go_106 ::
  MAlonzo.Code.Utils.T__'215'__428
    (MAlonzo.Code.Utils.T_Either_6
       T_NICSimplifierTag_4 T_ICSimplifierTag_8)
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_70
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     (MAlonzo.Code.Utils.T_Either_6
        T_NICSimplifierTag_4 T_ICSimplifierTag_8)
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_70
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  T_Trace_78
du_go_106 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__442 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Utils.C__'44'__442 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Utils.C__'44'__442 v6 v7
                      -> case coe v1 of
                           []
                             -> coe
                                  C_step_82 (coe v2) (coe v4) (coe v6) (coe C_done_84 (coe v7))
                           (:) v8 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Utils.C__'44'__442 v10 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Utils.C__'44'__442 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Utils.C__'44'__442 v14 v15
                                                  -> coe
                                                       C_step_82 (coe v2) (coe v4) (coe v6)
                                                       (coe
                                                          du_go_106
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
d_EvalResult_132 = ()
type T_EvalResult_132 = EvalResult
pattern C_success_134 a0 a1 = EvalSuccess a0 a1
pattern C_failure_136 a0 a1 a2 = EvalFailure a0 a1 a2
check_success_134 :: Integer -> Integer -> T_EvalResult_132
check_success_134 = EvalSuccess
check_failure_136 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Integer -> T_EvalResult_132
check_failure_136 = EvalFailure
cover_EvalResult_132 :: EvalResult -> ()
cover_EvalResult_132 x
  = case x of
      EvalSuccess _ _ -> ()
      EvalFailure _ _ _ -> ()
