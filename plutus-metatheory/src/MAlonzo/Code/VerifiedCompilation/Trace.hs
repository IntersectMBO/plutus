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

import UntypedPlutusCore.Transform.Certify.Trace
import qualified UntypedPlutusCore.Transform.Certify.Hints as Hints
import FFI.CostInfo
-- VerifiedCompilation.Trace.UncertifiedOptTag
d_UncertifiedOptTag_4 = ()
type T_UncertifiedOptTag_4 = UncertifiedOptStage
pattern C_caseOfCaseT_6 = CaseOfCase
pattern C_letFloatOutT_8 = LetFloatOut
pattern C_caseReduceT_10 = CaseReduce
check_caseOfCaseT_6 :: T_UncertifiedOptTag_4
check_caseOfCaseT_6 = CaseOfCase
check_letFloatOutT_8 :: T_UncertifiedOptTag_4
check_letFloatOutT_8 = LetFloatOut
check_caseReduceT_10 :: T_UncertifiedOptTag_4
check_caseReduceT_10 = CaseReduce
cover_UncertifiedOptTag_4 :: UncertifiedOptStage -> ()
cover_UncertifiedOptTag_4 x
  = case x of
      CaseOfCase -> ()
      LetFloatOut -> ()
      CaseReduce -> ()
-- VerifiedCompilation.Trace.CertifiedOptTag
d_CertifiedOptTag_12 = ()
type T_CertifiedOptTag_12 = CertifiedOptStage
pattern C_floatDelayT_14 = FloatDelay
pattern C_forceDelayT_16 = ForceDelay
pattern C_forceCaseDelayT_18 = ForceCaseDelay
pattern C_inlineT_20 = Inline
pattern C_cseT_22 = CSE
pattern C_applyToCaseT_24 = ApplyToCase
check_floatDelayT_14 :: T_CertifiedOptTag_12
check_floatDelayT_14 = FloatDelay
check_forceDelayT_16 :: T_CertifiedOptTag_12
check_forceDelayT_16 = ForceDelay
check_forceCaseDelayT_18 :: T_CertifiedOptTag_12
check_forceCaseDelayT_18 = ForceCaseDelay
check_inlineT_20 :: T_CertifiedOptTag_12
check_inlineT_20 = Inline
check_cseT_22 :: T_CertifiedOptTag_12
check_cseT_22 = CSE
check_applyToCaseT_24 :: T_CertifiedOptTag_12
check_applyToCaseT_24 = ApplyToCase
cover_CertifiedOptTag_12 :: CertifiedOptStage -> ()
cover_CertifiedOptTag_12 x
  = case x of
      FloatDelay -> ()
      ForceDelay -> ()
      ForceCaseDelay -> ()
      Inline -> ()
      CSE -> ()
      ApplyToCase -> ()
-- VerifiedCompilation.Trace.OptTag
d_OptTag_26 :: ()
d_OptTag_26 = erased
-- VerifiedCompilation.Trace.FloatDelayT
d_FloatDelayT_28 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_FloatDelayT_28
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_floatDelayT_14)
-- VerifiedCompilation.Trace.ForceDelayT
d_ForceDelayT_30 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_ForceDelayT_30
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_forceDelayT_16)
-- VerifiedCompilation.Trace.ForceCaseDelayT
d_ForceCaseDelayT_32 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_ForceCaseDelayT_32
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_forceCaseDelayT_18)
-- VerifiedCompilation.Trace.InlineT
d_InlineT_34 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_InlineT_34
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_inlineT_20)
-- VerifiedCompilation.Trace.CseT
d_CseT_36 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_CseT_36 = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_cseT_22)
-- VerifiedCompilation.Trace.ApplyToCaseT
d_ApplyToCaseT_38 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_ApplyToCaseT_38
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_applyToCaseT_24)
-- VerifiedCompilation.Trace.CaseOfCaseT
d_CaseOfCaseT_40 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_CaseOfCaseT_40
  = coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_caseOfCaseT_6)
-- VerifiedCompilation.Trace.LetFloatOutT
d_LetFloatOutT_42 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_LetFloatOutT_42
  = coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_letFloatOutT_8)
-- VerifiedCompilation.Trace.CaseReduceT
d_CaseReduceT_44 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_CaseReduceT_44
  = coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_caseReduceT_10)
-- VerifiedCompilation.Trace.InlineHints
d_InlineHints_46 = ()
type T_InlineHints_46 = Hints.Inline
pattern C_var_48 = Hints.InlVar
pattern C_expand_50 a0 = Hints.InlExpand a0
pattern C_ƛ_52 a0 = Hints.InlLam a0
pattern C__'183'__54 a0 a1 = Hints.InlApply a0 a1
pattern C__'183''8595'_56 a0 = Hints.InlDrop a0
pattern C_force_58 a0 = Hints.InlForce a0
pattern C_delay_60 a0 = Hints.InlDelay a0
pattern C_con_62 = Hints.InlCon
pattern C_builtin_64 = Hints.InlBuiltin
pattern C_error_66 = Hints.InlError
pattern C_constr_68 a0 = Hints.InlConstr a0
pattern C_case_70 a0 a1 = Hints.InlCase a0 a1
check_var_48 :: T_InlineHints_46
check_var_48 = Hints.InlVar
check_expand_50 :: T_InlineHints_46 -> T_InlineHints_46
check_expand_50 = Hints.InlExpand
check_ƛ_52 :: T_InlineHints_46 -> T_InlineHints_46
check_ƛ_52 = Hints.InlLam
check__'183'__54 ::
  T_InlineHints_46 -> T_InlineHints_46 -> T_InlineHints_46
check__'183'__54 = Hints.InlApply
check__'183''8595'_56 :: T_InlineHints_46 -> T_InlineHints_46
check__'183''8595'_56 = Hints.InlDrop
check_force_58 :: T_InlineHints_46 -> T_InlineHints_46
check_force_58 = Hints.InlForce
check_delay_60 :: T_InlineHints_46 -> T_InlineHints_46
check_delay_60 = Hints.InlDelay
check_con_62 :: T_InlineHints_46
check_con_62 = Hints.InlCon
check_builtin_64 :: T_InlineHints_46
check_builtin_64 = Hints.InlBuiltin
check_error_66 :: T_InlineHints_46
check_error_66 = Hints.InlError
check_constr_68 ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_46 ->
  T_InlineHints_46
check_constr_68 = Hints.InlConstr
check_case_70 ::
  T_InlineHints_46 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_46 ->
  T_InlineHints_46
check_case_70 = Hints.InlCase
cover_InlineHints_46 :: Hints.Inline -> ()
cover_InlineHints_46 x
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
d_Hints_72 = ()
type T_Hints_72 = Hints.Hints
pattern C_inline_74 a0 = Hints.Inline a0
pattern C_none_76 = Hints.NoHints
check_inline_74 :: T_InlineHints_46 -> T_Hints_72
check_inline_74 = Hints.Inline
check_none_76 :: T_Hints_72
check_none_76 = Hints.NoHints
cover_Hints_72 :: Hints.Hints -> ()
cover_Hints_72 x
  = case x of
      Hints.Inline _ -> ()
      Hints.NoHints -> ()
-- VerifiedCompilation.Trace.Trace
d_Trace_80 a0 = ()
data T_Trace_80
  = C_step_84 (MAlonzo.Code.Utils.T_Either_6
                 T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
              T_Hints_72 AgdaAny T_Trace_80 |
    C_done_86 AgdaAny
-- VerifiedCompilation.Trace.head
d_head_90 :: T_Trace_80 -> AgdaAny
d_head_90 v0
  = case coe v0 of
      C_step_84 v1 v2 v3 v4 -> coe v3
      C_done_86 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace.Dump
d_Dump_96 :: ()
d_Dump_96 = erased
-- VerifiedCompilation.Trace.toTrace
d_toTrace_98 ::
  [MAlonzo.Code.Utils.T__'215'__428
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_72
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  Maybe T_Trace_80
d_toTrace_98 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_go_108 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace._.go
d_go_108 ::
  MAlonzo.Code.Utils.T__'215'__428
    (MAlonzo.Code.Utils.T_Either_6
       T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_72
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_72
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  MAlonzo.Code.Utils.T__'215'__428
    (MAlonzo.Code.Utils.T_Either_6
       T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_72
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_72
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  T_Trace_80
d_go_108 ~v0 ~v1 v2 v3 = du_go_108 v2 v3
du_go_108 ::
  MAlonzo.Code.Utils.T__'215'__428
    (MAlonzo.Code.Utils.T_Either_6
       T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_72
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_72
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  T_Trace_80
du_go_108 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__442 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Utils.C__'44'__442 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Utils.C__'44'__442 v6 v7
                      -> case coe v1 of
                           []
                             -> coe
                                  C_step_84 (coe v2) (coe v4) (coe v6) (coe C_done_86 (coe v7))
                           (:) v8 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Utils.C__'44'__442 v10 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Utils.C__'44'__442 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Utils.C__'44'__442 v14 v15
                                                  -> coe
                                                       C_step_84 (coe v2) (coe v4) (coe v6)
                                                       (coe
                                                          du_go_108
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
d_EvalResult_134 = ()
type T_EvalResult_134 = EvalResult
pattern C_success_136 a0 a1 = EvalSuccess a0 a1
pattern C_failure_138 a0 a1 a2 = EvalFailure a0 a1 a2
check_success_136 :: Integer -> Integer -> T_EvalResult_134
check_success_136 = EvalSuccess
check_failure_138 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Integer -> T_EvalResult_134
check_failure_138 = EvalFailure
cover_EvalResult_134 :: EvalResult -> ()
cover_EvalResult_134 x
  = case x of
      EvalSuccess _ _ -> ()
      EvalFailure _ _ _ -> ()
