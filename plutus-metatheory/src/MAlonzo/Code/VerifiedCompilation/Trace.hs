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
pattern C_polyBuiltinT_10 = PolyBuiltin
check_caseOfCaseT_6 :: T_UncertifiedOptTag_4
check_caseOfCaseT_6 = CaseOfCase
check_constantFoldingT_8 :: T_UncertifiedOptTag_4
check_constantFoldingT_8 = ConstantFolding
check_polyBuiltinT_10 :: T_UncertifiedOptTag_4
check_polyBuiltinT_10 = PolyBuiltin
cover_UncertifiedOptTag_4 :: UncertifiedOptStage -> ()
cover_UncertifiedOptTag_4 x
  = case x of
      CaseOfCase -> ()
      ConstantFolding -> ()
      PolyBuiltin -> ()
-- VerifiedCompilation.Trace.CertifiedOptTag
d_CertifiedOptTag_12 = ()
type T_CertifiedOptTag_12 = CertifiedOptStage
pattern C_floatDelayT_14 = FloatDelay
pattern C_forceDelayT_16 = ForceDelay
pattern C_forceCaseDelayT_18 = ForceCaseDelay
pattern C_inlineT_20 = Inline
pattern C_cseT_22 = CSE
pattern C_applyToCaseT_24 = ApplyToCase
pattern C_caseReduceT_26 = CaseReduce
pattern C_letFloatOutT_28 = LetFloatOut
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
check_caseReduceT_26 :: T_CertifiedOptTag_12
check_caseReduceT_26 = CaseReduce
check_letFloatOutT_28 :: T_CertifiedOptTag_12
check_letFloatOutT_28 = LetFloatOut
cover_CertifiedOptTag_12 :: CertifiedOptStage -> ()
cover_CertifiedOptTag_12 x
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
d_OptTag_30 :: ()
d_OptTag_30 = erased
-- VerifiedCompilation.Trace.FloatDelayT
d_FloatDelayT_32 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_FloatDelayT_32
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_floatDelayT_14)
-- VerifiedCompilation.Trace.ForceDelayT
d_ForceDelayT_34 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_ForceDelayT_34
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_forceDelayT_16)
-- VerifiedCompilation.Trace.ForceCaseDelayT
d_ForceCaseDelayT_36 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_ForceCaseDelayT_36
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_forceCaseDelayT_18)
-- VerifiedCompilation.Trace.InlineT
d_InlineT_38 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_InlineT_38
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_inlineT_20)
-- VerifiedCompilation.Trace.CseT
d_CseT_40 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_CseT_40 = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_cseT_22)
-- VerifiedCompilation.Trace.ApplyToCaseT
d_ApplyToCaseT_42 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_ApplyToCaseT_42
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_applyToCaseT_24)
-- VerifiedCompilation.Trace.LetFloatOutT
d_LetFloatOutT_44 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_LetFloatOutT_44
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_letFloatOutT_28)
-- VerifiedCompilation.Trace.CaseReduceT
d_CaseReduceT_46 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_CaseReduceT_46
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_caseReduceT_26)
-- VerifiedCompilation.Trace.CaseOfCaseT
d_CaseOfCaseT_48 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_CaseOfCaseT_48
  = coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_caseOfCaseT_6)
-- VerifiedCompilation.Trace.ConstantFoldingT
d_ConstantFoldingT_50 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_ConstantFoldingT_50
  = coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_constantFoldingT_8)
-- VerifiedCompilation.Trace.PolyBuiltinT
d_PolyBuiltinT_52 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_PolyBuiltinT_52
  = coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_polyBuiltinT_10)
-- VerifiedCompilation.Trace.InlineHints
d_InlineHints_54 = ()
type T_InlineHints_54 = Hints.Inline
pattern C_var_56 = Hints.InlVar
pattern C_expand_58 a0 = Hints.InlExpand a0
pattern C_ƛ_60 a0 = Hints.InlLam a0
pattern C__'183'__62 a0 a1 = Hints.InlApply a0 a1
pattern C__'183''8595'_64 a0 = Hints.InlDrop a0
pattern C_force_66 a0 = Hints.InlForce a0
pattern C_delay_68 a0 = Hints.InlDelay a0
pattern C_con_70 = Hints.InlCon
pattern C_builtin_72 = Hints.InlBuiltin
pattern C_error_74 = Hints.InlError
pattern C_constr_76 a0 = Hints.InlConstr a0
pattern C_case_78 a0 a1 = Hints.InlCase a0 a1
check_var_56 :: T_InlineHints_54
check_var_56 = Hints.InlVar
check_expand_58 :: T_InlineHints_54 -> T_InlineHints_54
check_expand_58 = Hints.InlExpand
check_ƛ_60 :: T_InlineHints_54 -> T_InlineHints_54
check_ƛ_60 = Hints.InlLam
check__'183'__62 ::
  T_InlineHints_54 -> T_InlineHints_54 -> T_InlineHints_54
check__'183'__62 = Hints.InlApply
check__'183''8595'_64 :: T_InlineHints_54 -> T_InlineHints_54
check__'183''8595'_64 = Hints.InlDrop
check_force_66 :: T_InlineHints_54 -> T_InlineHints_54
check_force_66 = Hints.InlForce
check_delay_68 :: T_InlineHints_54 -> T_InlineHints_54
check_delay_68 = Hints.InlDelay
check_con_70 :: T_InlineHints_54
check_con_70 = Hints.InlCon
check_builtin_72 :: T_InlineHints_54
check_builtin_72 = Hints.InlBuiltin
check_error_74 :: T_InlineHints_54
check_error_74 = Hints.InlError
check_constr_76 ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_54 ->
  T_InlineHints_54
check_constr_76 = Hints.InlConstr
check_case_78 ::
  T_InlineHints_54 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_54 ->
  T_InlineHints_54
check_case_78 = Hints.InlCase
cover_InlineHints_54 :: Hints.Inline -> ()
cover_InlineHints_54 x
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
d_Hints_80 = ()
type T_Hints_80 = Hints.Hints
pattern C_inline_82 a0 = Hints.Inline a0
pattern C_none_84 = Hints.NoHints
check_inline_82 :: T_InlineHints_54 -> T_Hints_80
check_inline_82 = Hints.Inline
check_none_84 :: T_Hints_80
check_none_84 = Hints.NoHints
cover_Hints_80 :: Hints.Hints -> ()
cover_Hints_80 x
  = case x of
      Hints.Inline _ -> ()
      Hints.NoHints -> ()
-- VerifiedCompilation.Trace.Trace
d_Trace_88 a0 = ()
data T_Trace_88
  = C_step_92 (MAlonzo.Code.Utils.T_Either_6
                 T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
              T_Hints_80 AgdaAny T_Trace_88 |
    C_done_94 AgdaAny
-- VerifiedCompilation.Trace.head
d_head_98 :: T_Trace_88 -> AgdaAny
d_head_98 v0
  = case coe v0 of
      C_step_92 v1 v2 v3 v4 -> coe v3
      C_done_94 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace.Dump
d_Dump_104 :: ()
d_Dump_104 = erased
-- VerifiedCompilation.Trace.toTrace
d_toTrace_106 ::
  [MAlonzo.Code.Utils.T__'215'__436
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
     (MAlonzo.Code.Utils.T__'215'__436
        T_Hints_80
        (MAlonzo.Code.Utils.T__'215'__436
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  Maybe T_Trace_88
d_toTrace_106 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_go_116 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace._.go
d_go_116 ::
  MAlonzo.Code.Utils.T__'215'__436
    (MAlonzo.Code.Utils.T_Either_6
       T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
    (MAlonzo.Code.Utils.T__'215'__436
       T_Hints_80
       (MAlonzo.Code.Utils.T__'215'__436
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__436
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
     (MAlonzo.Code.Utils.T__'215'__436
        T_Hints_80
        (MAlonzo.Code.Utils.T__'215'__436
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  MAlonzo.Code.Utils.T__'215'__436
    (MAlonzo.Code.Utils.T_Either_6
       T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
    (MAlonzo.Code.Utils.T__'215'__436
       T_Hints_80
       (MAlonzo.Code.Utils.T__'215'__436
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__436
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
     (MAlonzo.Code.Utils.T__'215'__436
        T_Hints_80
        (MAlonzo.Code.Utils.T__'215'__436
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  T_Trace_88
d_go_116 ~v0 ~v1 v2 v3 = du_go_116 v2 v3
du_go_116 ::
  MAlonzo.Code.Utils.T__'215'__436
    (MAlonzo.Code.Utils.T_Either_6
       T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
    (MAlonzo.Code.Utils.T__'215'__436
       T_Hints_80
       (MAlonzo.Code.Utils.T__'215'__436
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__436
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
     (MAlonzo.Code.Utils.T__'215'__436
        T_Hints_80
        (MAlonzo.Code.Utils.T__'215'__436
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  T_Trace_88
du_go_116 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__450 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Utils.C__'44'__450 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Utils.C__'44'__450 v6 v7
                      -> case coe v1 of
                           []
                             -> coe
                                  C_step_92 (coe v2) (coe v4) (coe v6) (coe C_done_94 (coe v7))
                           (:) v8 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Utils.C__'44'__450 v10 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Utils.C__'44'__450 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Utils.C__'44'__450 v14 v15
                                                  -> coe
                                                       C_step_92 (coe v2) (coe v4) (coe v6)
                                                       (coe
                                                          du_go_116
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
d_EvalResult_142 = ()
type T_EvalResult_142 = EvalResult
pattern C_success_144 a0 a1 = EvalSuccess a0 a1
pattern C_failure_146 a0 a1 a2 = EvalFailure a0 a1 a2
check_success_144 :: Integer -> Integer -> T_EvalResult_142
check_success_144 = EvalSuccess
check_failure_146 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Integer -> T_EvalResult_142
check_failure_146 = EvalFailure
cover_EvalResult_142 :: EvalResult -> ()
cover_EvalResult_142 x
  = case x of
      EvalSuccess _ _ -> ()
      EvalFailure _ _ _ -> ()
