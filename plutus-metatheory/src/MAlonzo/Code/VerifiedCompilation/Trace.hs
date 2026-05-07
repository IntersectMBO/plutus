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
pattern C_constantFoldingT_8 = ConstantFolding
check_caseOfCaseT_6 :: T_UncertifiedOptTag_4
check_caseOfCaseT_6 = CaseOfCase
check_constantFoldingT_8 :: T_UncertifiedOptTag_4
check_constantFoldingT_8 = ConstantFolding
cover_UncertifiedOptTag_4 :: UncertifiedOptStage -> ()
cover_UncertifiedOptTag_4 x
  = case x of
      CaseOfCase -> ()
      ConstantFolding -> ()
-- VerifiedCompilation.Trace.CertifiedOptTag
d_CertifiedOptTag_10 = ()
type T_CertifiedOptTag_10 = CertifiedOptStage
pattern C_floatDelayT_12 = FloatDelay
pattern C_forceDelayT_14 = ForceDelay
pattern C_forceCaseDelayT_16 = ForceCaseDelay
pattern C_inlineT_18 = Inline
pattern C_cseT_20 = CSE
pattern C_applyToCaseT_22 = ApplyToCase
pattern C_caseReduceT_24 = CaseReduce
pattern C_letFloatOutT_26 = LetFloatOut
check_floatDelayT_12 :: T_CertifiedOptTag_10
check_floatDelayT_12 = FloatDelay
check_forceDelayT_14 :: T_CertifiedOptTag_10
check_forceDelayT_14 = ForceDelay
check_forceCaseDelayT_16 :: T_CertifiedOptTag_10
check_forceCaseDelayT_16 = ForceCaseDelay
check_inlineT_18 :: T_CertifiedOptTag_10
check_inlineT_18 = Inline
check_cseT_20 :: T_CertifiedOptTag_10
check_cseT_20 = CSE
check_applyToCaseT_22 :: T_CertifiedOptTag_10
check_applyToCaseT_22 = ApplyToCase
check_caseReduceT_24 :: T_CertifiedOptTag_10
check_caseReduceT_24 = CaseReduce
check_letFloatOutT_26 :: T_CertifiedOptTag_10
check_letFloatOutT_26 = LetFloatOut
cover_CertifiedOptTag_10 :: CertifiedOptStage -> ()
cover_CertifiedOptTag_10 x
  = case x of
      FloatDelay -> ()
      ForceDelay -> ()
      ForceCaseDelay -> ()
      Inline -> ()
      CSE -> ()
      ApplyToCase -> ()
      CaseReduce -> ()
      LetFloatOut -> ()
-- VerifiedCompilation.Trace.OptTag
d_OptTag_28 :: ()
d_OptTag_28 = erased
-- VerifiedCompilation.Trace.FloatDelayT
d_FloatDelayT_30 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_10
d_FloatDelayT_30
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_floatDelayT_12)
-- VerifiedCompilation.Trace.ForceDelayT
d_ForceDelayT_32 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_10
d_ForceDelayT_32
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_forceDelayT_14)
-- VerifiedCompilation.Trace.ForceCaseDelayT
d_ForceCaseDelayT_34 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_10
d_ForceCaseDelayT_34
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_forceCaseDelayT_16)
-- VerifiedCompilation.Trace.InlineT
d_InlineT_36 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_10
d_InlineT_36
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_inlineT_18)
-- VerifiedCompilation.Trace.CseT
d_CseT_38 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_10
d_CseT_38 = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_cseT_20)
-- VerifiedCompilation.Trace.ApplyToCaseT
d_ApplyToCaseT_40 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_10
d_ApplyToCaseT_40
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_applyToCaseT_22)
-- VerifiedCompilation.Trace.LetFloatOutT
d_LetFloatOutT_42 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_10
d_LetFloatOutT_42
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_letFloatOutT_26)
-- VerifiedCompilation.Trace.CaseReduceT
d_CaseReduceT_44 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_10
d_CaseReduceT_44
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_caseReduceT_24)
-- VerifiedCompilation.Trace.CaseOfCaseT
d_CaseOfCaseT_46 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_10
d_CaseOfCaseT_46
  = coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_caseOfCaseT_6)
-- VerifiedCompilation.Trace.ConstantFoldingT
d_ConstantFoldingT_48 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_10
d_ConstantFoldingT_48
  = coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_constantFoldingT_8)
-- VerifiedCompilation.Trace.InlineHints
d_InlineHints_50 = ()
type T_InlineHints_50 = Hints.Inline
pattern C_var_52 = Hints.InlVar
pattern C_expand_54 a0 = Hints.InlExpand a0
pattern C_ƛ_56 a0 = Hints.InlLam a0
pattern C__'183'__58 a0 a1 = Hints.InlApply a0 a1
pattern C__'183''8595'_60 a0 = Hints.InlDrop a0
pattern C_force_62 a0 = Hints.InlForce a0
pattern C_delay_64 a0 = Hints.InlDelay a0
pattern C_con_66 = Hints.InlCon
pattern C_builtin_68 = Hints.InlBuiltin
pattern C_error_70 = Hints.InlError
pattern C_constr_72 a0 = Hints.InlConstr a0
pattern C_case_74 a0 a1 = Hints.InlCase a0 a1
check_var_52 :: T_InlineHints_50
check_var_52 = Hints.InlVar
check_expand_54 :: T_InlineHints_50 -> T_InlineHints_50
check_expand_54 = Hints.InlExpand
check_ƛ_56 :: T_InlineHints_50 -> T_InlineHints_50
check_ƛ_56 = Hints.InlLam
check__'183'__58 ::
  T_InlineHints_50 -> T_InlineHints_50 -> T_InlineHints_50
check__'183'__58 = Hints.InlApply
check__'183''8595'_60 :: T_InlineHints_50 -> T_InlineHints_50
check__'183''8595'_60 = Hints.InlDrop
check_force_62 :: T_InlineHints_50 -> T_InlineHints_50
check_force_62 = Hints.InlForce
check_delay_64 :: T_InlineHints_50 -> T_InlineHints_50
check_delay_64 = Hints.InlDelay
check_con_66 :: T_InlineHints_50
check_con_66 = Hints.InlCon
check_builtin_68 :: T_InlineHints_50
check_builtin_68 = Hints.InlBuiltin
check_error_70 :: T_InlineHints_50
check_error_70 = Hints.InlError
check_constr_72 ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_50 ->
  T_InlineHints_50
check_constr_72 = Hints.InlConstr
check_case_74 ::
  T_InlineHints_50 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_50 ->
  T_InlineHints_50
check_case_74 = Hints.InlCase
cover_InlineHints_50 :: Hints.Inline -> ()
cover_InlineHints_50 x
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
d_Hints_76 = ()
type T_Hints_76 = Hints.Hints
pattern C_inline_78 a0 = Hints.Inline a0
pattern C_none_80 = Hints.NoHints
check_inline_78 :: T_InlineHints_50 -> T_Hints_76
check_inline_78 = Hints.Inline
check_none_80 :: T_Hints_76
check_none_80 = Hints.NoHints
cover_Hints_76 :: Hints.Hints -> ()
cover_Hints_76 x
  = case x of
      Hints.Inline _ -> ()
      Hints.NoHints -> ()
-- VerifiedCompilation.Trace.Trace
d_Trace_84 a0 = ()
data T_Trace_84
  = C_step_88 (MAlonzo.Code.Utils.T_Either_6
                 T_UncertifiedOptTag_4 T_CertifiedOptTag_10)
              T_Hints_76 AgdaAny T_Trace_84 |
    C_done_90 AgdaAny
-- VerifiedCompilation.Trace.head
d_head_94 :: T_Trace_84 -> AgdaAny
d_head_94 v0
  = case coe v0 of
      C_step_88 v1 v2 v3 v4 -> coe v3
      C_done_90 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace.Dump
d_Dump_100 :: ()
d_Dump_100 = erased
-- VerifiedCompilation.Trace.toTrace
d_toTrace_102 ::
  [MAlonzo.Code.Utils.T__'215'__436
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_10)
     (MAlonzo.Code.Utils.T__'215'__436
        T_Hints_76
        (MAlonzo.Code.Utils.T__'215'__436
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  Maybe T_Trace_84
d_toTrace_102 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_go_112 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace._.go
d_go_112 ::
  MAlonzo.Code.Utils.T__'215'__436
    (MAlonzo.Code.Utils.T_Either_6
       T_UncertifiedOptTag_4 T_CertifiedOptTag_10)
    (MAlonzo.Code.Utils.T__'215'__436
       T_Hints_76
       (MAlonzo.Code.Utils.T__'215'__436
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__436
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_10)
     (MAlonzo.Code.Utils.T__'215'__436
        T_Hints_76
        (MAlonzo.Code.Utils.T__'215'__436
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  MAlonzo.Code.Utils.T__'215'__436
    (MAlonzo.Code.Utils.T_Either_6
       T_UncertifiedOptTag_4 T_CertifiedOptTag_10)
    (MAlonzo.Code.Utils.T__'215'__436
       T_Hints_76
       (MAlonzo.Code.Utils.T__'215'__436
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__436
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_10)
     (MAlonzo.Code.Utils.T__'215'__436
        T_Hints_76
        (MAlonzo.Code.Utils.T__'215'__436
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  T_Trace_84
d_go_112 ~v0 ~v1 v2 v3 = du_go_112 v2 v3
du_go_112 ::
  MAlonzo.Code.Utils.T__'215'__436
    (MAlonzo.Code.Utils.T_Either_6
       T_UncertifiedOptTag_4 T_CertifiedOptTag_10)
    (MAlonzo.Code.Utils.T__'215'__436
       T_Hints_76
       (MAlonzo.Code.Utils.T__'215'__436
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__436
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_10)
     (MAlonzo.Code.Utils.T__'215'__436
        T_Hints_76
        (MAlonzo.Code.Utils.T__'215'__436
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  T_Trace_84
du_go_112 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__450 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Utils.C__'44'__450 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Utils.C__'44'__450 v6 v7
                      -> case coe v1 of
                           []
                             -> coe
                                  C_step_88 (coe v2) (coe v4) (coe v6) (coe C_done_90 (coe v7))
                           (:) v8 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Utils.C__'44'__450 v10 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Utils.C__'44'__450 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Utils.C__'44'__450 v14 v15
                                                  -> coe
                                                       C_step_88 (coe v2) (coe v4) (coe v6)
                                                       (coe
                                                          du_go_112
                                                          (coe
                                                             MAlonzo.Code.Utils.C__'44'__450
                                                             (coe v10)
                                                             (coe
                                                                MAlonzo.Code.Utils.C__'44'__450
                                                                (coe v12)
                                                                (coe
                                                                   MAlonzo.Code.Utils.C__'44'__450
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
d_EvalResult_138 = ()
type T_EvalResult_138 = EvalResult
pattern C_success_140 a0 a1 = EvalSuccess a0 a1
pattern C_failure_142 a0 a1 a2 = EvalFailure a0 a1 a2
check_success_140 :: Integer -> Integer -> T_EvalResult_138
check_success_140 = EvalSuccess
check_failure_142 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Integer -> T_EvalResult_138
check_failure_142 = EvalFailure
cover_EvalResult_138 :: EvalResult -> ()
cover_EvalResult_138 x
  = case x of
      EvalSuccess _ _ -> ()
      EvalFailure _ _ _ -> ()
