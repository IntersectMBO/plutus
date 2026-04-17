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
pattern C_uncertifiedConstantFoldT_10 = UncertifiedConstantFold
check_caseOfCaseT_6 :: T_UncertifiedOptTag_4
check_caseOfCaseT_6 = CaseOfCase
check_letFloatOutT_8 :: T_UncertifiedOptTag_4
check_letFloatOutT_8 = LetFloatOut
check_uncertifiedConstantFoldT_10 :: T_UncertifiedOptTag_4
check_uncertifiedConstantFoldT_10 = UncertifiedConstantFold
cover_UncertifiedOptTag_4 :: UncertifiedOptStage -> ()
cover_UncertifiedOptTag_4 x
  = case x of
      CaseOfCase -> ()
      LetFloatOut -> ()
      UncertifiedConstantFold -> ()
-- VerifiedCompilation.Trace.CertifiedOptTag
d_CertifiedOptTag_12 = ()
type T_CertifiedOptTag_12 = CertifiedOptStage
pattern C_floatDelayT_14 = FloatDelay
pattern C_forceDelayT_16 = ForceDelay
pattern C_forceCaseDelayT_18 = ForceCaseDelay
pattern C_caseReduceT_20 = CaseReduce
pattern C_inlineT_22 = Inline
pattern C_cseT_24 = CSE
pattern C_applyToCaseT_26 = ApplyToCase
pattern C_constantFoldT_28 = ConstantFold
check_floatDelayT_14 :: T_CertifiedOptTag_12
check_floatDelayT_14 = FloatDelay
check_forceDelayT_16 :: T_CertifiedOptTag_12
check_forceDelayT_16 = ForceDelay
check_forceCaseDelayT_18 :: T_CertifiedOptTag_12
check_forceCaseDelayT_18 = ForceCaseDelay
check_caseReduceT_20 :: T_CertifiedOptTag_12
check_caseReduceT_20 = CaseReduce
check_inlineT_22 :: T_CertifiedOptTag_12
check_inlineT_22 = Inline
check_cseT_24 :: T_CertifiedOptTag_12
check_cseT_24 = CSE
check_applyToCaseT_26 :: T_CertifiedOptTag_12
check_applyToCaseT_26 = ApplyToCase
check_constantFoldT_28 :: T_CertifiedOptTag_12
check_constantFoldT_28 = ConstantFold
cover_CertifiedOptTag_12 :: CertifiedOptStage -> ()
cover_CertifiedOptTag_12 x
  = case x of
      FloatDelay -> ()
      ForceDelay -> ()
      ForceCaseDelay -> ()
      CaseReduce -> ()
      Inline -> ()
      CSE -> ()
      ApplyToCase -> ()
      ConstantFold -> ()
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
-- VerifiedCompilation.Trace.CaseReduceT
d_CaseReduceT_38 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_CaseReduceT_38
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_caseReduceT_20)
-- VerifiedCompilation.Trace.InlineT
d_InlineT_40 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_InlineT_40
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_inlineT_22)
-- VerifiedCompilation.Trace.CseT
d_CseT_42 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_CseT_42 = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_cseT_24)
-- VerifiedCompilation.Trace.ApplyToCaseT
d_ApplyToCaseT_44 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_ApplyToCaseT_44
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_applyToCaseT_26)
-- VerifiedCompilation.Trace.ConstantFoldT
d_ConstantFoldT_46 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_ConstantFoldT_46
  = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_constantFoldT_28)
-- VerifiedCompilation.Trace.CaseOfCaseT
d_CaseOfCaseT_48 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_CaseOfCaseT_48
  = coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_caseOfCaseT_6)
-- VerifiedCompilation.Trace.LetFloatOutT
d_LetFloatOutT_50 ::
  MAlonzo.Code.Utils.T_Either_6
    T_UncertifiedOptTag_4 T_CertifiedOptTag_12
d_LetFloatOutT_50
  = coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_letFloatOutT_8)
-- VerifiedCompilation.Trace.CertifiedBuiltin
d_CertifiedBuiltin_52 = ()
type T_CertifiedBuiltin_52 = CertifiedBuiltin
pattern C_certAddInteger_54 = CertAddInteger
pattern C_certSubtractInteger_56 = CertSubtractInteger
pattern C_certMultiplyInteger_58 = CertMultiplyInteger
pattern C_certDivideInteger_60 = CertDivideInteger
pattern C_certQuotientInteger_62 = CertQuotientInteger
pattern C_certRemainderInteger_64 = CertRemainderInteger
pattern C_certModInteger_66 = CertModInteger
pattern C_certEqualsInteger_68 = CertEqualsInteger
pattern C_certLessThanInteger_70 = CertLessThanInteger
pattern C_certLessThanEqualsInteger_72 = CertLessThanEqualsInteger
pattern C_certIfThenElse_74 = CertIfThenElse
pattern C_certChooseUnit_76 = CertChooseUnit
pattern C_certFstPair_78 = CertFstPair
pattern C_certSndPair_80 = CertSndPair
pattern C_certChooseList_82 = CertChooseList
pattern C_certMkCons_84 = CertMkCons
pattern C_certHeadList_86 = CertHeadList
pattern C_certTailList_88 = CertTailList
pattern C_certNullList_90 = CertNullList
pattern C_certDropList_92 = CertDropList
pattern C_certChooseData_94 = CertChooseData
pattern C_certConstrData_96 = CertConstrData
pattern C_certMapData_98 = CertMapData
pattern C_certListData_100 = CertListData
pattern C_certIData_102 = CertIData
pattern C_certUnConstrData_104 = CertUnConstrData
pattern C_certUnMapData_106 = CertUnMapData
pattern C_certUnListData_108 = CertUnListData
pattern C_certUnIData_110 = CertUnIData
pattern C_certEqualsData_112 = CertEqualsData
pattern C_certMkPairData_114 = CertMkPairData
pattern C_certMkNilData_116 = CertMkNilData
pattern C_certMkNilPairData_118 = CertMkNilPairData
check_certAddInteger_54 :: T_CertifiedBuiltin_52
check_certAddInteger_54 = CertAddInteger
check_certSubtractInteger_56 :: T_CertifiedBuiltin_52
check_certSubtractInteger_56 = CertSubtractInteger
check_certMultiplyInteger_58 :: T_CertifiedBuiltin_52
check_certMultiplyInteger_58 = CertMultiplyInteger
check_certDivideInteger_60 :: T_CertifiedBuiltin_52
check_certDivideInteger_60 = CertDivideInteger
check_certQuotientInteger_62 :: T_CertifiedBuiltin_52
check_certQuotientInteger_62 = CertQuotientInteger
check_certRemainderInteger_64 :: T_CertifiedBuiltin_52
check_certRemainderInteger_64 = CertRemainderInteger
check_certModInteger_66 :: T_CertifiedBuiltin_52
check_certModInteger_66 = CertModInteger
check_certEqualsInteger_68 :: T_CertifiedBuiltin_52
check_certEqualsInteger_68 = CertEqualsInteger
check_certLessThanInteger_70 :: T_CertifiedBuiltin_52
check_certLessThanInteger_70 = CertLessThanInteger
check_certLessThanEqualsInteger_72 :: T_CertifiedBuiltin_52
check_certLessThanEqualsInteger_72 = CertLessThanEqualsInteger
check_certIfThenElse_74 :: T_CertifiedBuiltin_52
check_certIfThenElse_74 = CertIfThenElse
check_certChooseUnit_76 :: T_CertifiedBuiltin_52
check_certChooseUnit_76 = CertChooseUnit
check_certFstPair_78 :: T_CertifiedBuiltin_52
check_certFstPair_78 = CertFstPair
check_certSndPair_80 :: T_CertifiedBuiltin_52
check_certSndPair_80 = CertSndPair
check_certChooseList_82 :: T_CertifiedBuiltin_52
check_certChooseList_82 = CertChooseList
check_certMkCons_84 :: T_CertifiedBuiltin_52
check_certMkCons_84 = CertMkCons
check_certHeadList_86 :: T_CertifiedBuiltin_52
check_certHeadList_86 = CertHeadList
check_certTailList_88 :: T_CertifiedBuiltin_52
check_certTailList_88 = CertTailList
check_certNullList_90 :: T_CertifiedBuiltin_52
check_certNullList_90 = CertNullList
check_certDropList_92 :: T_CertifiedBuiltin_52
check_certDropList_92 = CertDropList
check_certChooseData_94 :: T_CertifiedBuiltin_52
check_certChooseData_94 = CertChooseData
check_certConstrData_96 :: T_CertifiedBuiltin_52
check_certConstrData_96 = CertConstrData
check_certMapData_98 :: T_CertifiedBuiltin_52
check_certMapData_98 = CertMapData
check_certListData_100 :: T_CertifiedBuiltin_52
check_certListData_100 = CertListData
check_certIData_102 :: T_CertifiedBuiltin_52
check_certIData_102 = CertIData
check_certUnConstrData_104 :: T_CertifiedBuiltin_52
check_certUnConstrData_104 = CertUnConstrData
check_certUnMapData_106 :: T_CertifiedBuiltin_52
check_certUnMapData_106 = CertUnMapData
check_certUnListData_108 :: T_CertifiedBuiltin_52
check_certUnListData_108 = CertUnListData
check_certUnIData_110 :: T_CertifiedBuiltin_52
check_certUnIData_110 = CertUnIData
check_certEqualsData_112 :: T_CertifiedBuiltin_52
check_certEqualsData_112 = CertEqualsData
check_certMkPairData_114 :: T_CertifiedBuiltin_52
check_certMkPairData_114 = CertMkPairData
check_certMkNilData_116 :: T_CertifiedBuiltin_52
check_certMkNilData_116 = CertMkNilData
check_certMkNilPairData_118 :: T_CertifiedBuiltin_52
check_certMkNilPairData_118 = CertMkNilPairData
cover_CertifiedBuiltin_52 :: CertifiedBuiltin -> ()
cover_CertifiedBuiltin_52 x
  = case x of
      CertAddInteger -> ()
      CertSubtractInteger -> ()
      CertMultiplyInteger -> ()
      CertDivideInteger -> ()
      CertQuotientInteger -> ()
      CertRemainderInteger -> ()
      CertModInteger -> ()
      CertEqualsInteger -> ()
      CertLessThanInteger -> ()
      CertLessThanEqualsInteger -> ()
      CertIfThenElse -> ()
      CertChooseUnit -> ()
      CertFstPair -> ()
      CertSndPair -> ()
      CertChooseList -> ()
      CertMkCons -> ()
      CertHeadList -> ()
      CertTailList -> ()
      CertNullList -> ()
      CertDropList -> ()
      CertChooseData -> ()
      CertConstrData -> ()
      CertMapData -> ()
      CertListData -> ()
      CertIData -> ()
      CertUnConstrData -> ()
      CertUnMapData -> ()
      CertUnListData -> ()
      CertUnIData -> ()
      CertEqualsData -> ()
      CertMkPairData -> ()
      CertMkNilData -> ()
      CertMkNilPairData -> ()
-- VerifiedCompilation.Trace.InlineHints
d_InlineHints_120 = ()
type T_InlineHints_120 = Hints.Inline
pattern C_var_122 = Hints.InlVar
pattern C_expand_124 a0 = Hints.InlExpand a0
pattern C_ƛ_126 a0 = Hints.InlLam a0
pattern C__'183'__128 a0 a1 = Hints.InlApply a0 a1
pattern C__'183''8595'_130 a0 = Hints.InlDrop a0
pattern C_force_132 a0 = Hints.InlForce a0
pattern C_delay_134 a0 = Hints.InlDelay a0
pattern C_con_136 = Hints.InlCon
pattern C_builtin_138 = Hints.InlBuiltin
pattern C_error_140 = Hints.InlError
pattern C_constr_142 a0 = Hints.InlConstr a0
pattern C_case_144 a0 a1 = Hints.InlCase a0 a1
check_var_122 :: T_InlineHints_120
check_var_122 = Hints.InlVar
check_expand_124 :: T_InlineHints_120 -> T_InlineHints_120
check_expand_124 = Hints.InlExpand
check_ƛ_126 :: T_InlineHints_120 -> T_InlineHints_120
check_ƛ_126 = Hints.InlLam
check__'183'__128 ::
  T_InlineHints_120 -> T_InlineHints_120 -> T_InlineHints_120
check__'183'__128 = Hints.InlApply
check__'183''8595'_130 :: T_InlineHints_120 -> T_InlineHints_120
check__'183''8595'_130 = Hints.InlDrop
check_force_132 :: T_InlineHints_120 -> T_InlineHints_120
check_force_132 = Hints.InlForce
check_delay_134 :: T_InlineHints_120 -> T_InlineHints_120
check_delay_134 = Hints.InlDelay
check_con_136 :: T_InlineHints_120
check_con_136 = Hints.InlCon
check_builtin_138 :: T_InlineHints_120
check_builtin_138 = Hints.InlBuiltin
check_error_140 :: T_InlineHints_120
check_error_140 = Hints.InlError
check_constr_142 ::
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_120 ->
  T_InlineHints_120
check_constr_142 = Hints.InlConstr
check_case_144 ::
  T_InlineHints_120 ->
  MAlonzo.Code.Agda.Builtin.List.T_List_10 () T_InlineHints_120 ->
  T_InlineHints_120
check_case_144 = Hints.InlCase
cover_InlineHints_120 :: Hints.Inline -> ()
cover_InlineHints_120 x
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
d_Hints_146 = ()
type T_Hints_146 = Hints.Hints
pattern C_inline_148 a0 = Hints.Inline a0
pattern C_none_150 = Hints.NoHints
check_inline_148 :: T_InlineHints_120 -> T_Hints_146
check_inline_148 = Hints.Inline
check_none_150 :: T_Hints_146
check_none_150 = Hints.NoHints
cover_Hints_146 :: Hints.Hints -> ()
cover_Hints_146 x
  = case x of
      Hints.Inline _ -> ()
      Hints.NoHints -> ()
-- VerifiedCompilation.Trace.Trace
d_Trace_154 a0 = ()
data T_Trace_154
  = C_step_158 (MAlonzo.Code.Utils.T_Either_6
                  T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
               T_Hints_146 AgdaAny T_Trace_154 |
    C_done_160 AgdaAny
-- VerifiedCompilation.Trace.head
d_head_164 :: T_Trace_154 -> AgdaAny
d_head_164 v0
  = case coe v0 of
      C_step_158 v1 v2 v3 v4 -> coe v3
      C_done_160 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace.Dump
d_Dump_170 :: ()
d_Dump_170 = erased
-- VerifiedCompilation.Trace.toTrace
d_toTrace_172 ::
  [MAlonzo.Code.Utils.T__'215'__428
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_146
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  Maybe T_Trace_154
d_toTrace_172 v0
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_go_182 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace._.go
d_go_182 ::
  MAlonzo.Code.Utils.T__'215'__428
    (MAlonzo.Code.Utils.T_Either_6
       T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_146
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_146
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  MAlonzo.Code.Utils.T__'215'__428
    (MAlonzo.Code.Utils.T_Either_6
       T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_146
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_146
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  T_Trace_154
d_go_182 ~v0 ~v1 v2 v3 = du_go_182 v2 v3
du_go_182 ::
  MAlonzo.Code.Utils.T__'215'__428
    (MAlonzo.Code.Utils.T_Either_6
       T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
    (MAlonzo.Code.Utils.T__'215'__428
       T_Hints_146
       (MAlonzo.Code.Utils.T__'215'__428
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  [MAlonzo.Code.Utils.T__'215'__428
     (MAlonzo.Code.Utils.T_Either_6
        T_UncertifiedOptTag_4 T_CertifiedOptTag_12)
     (MAlonzo.Code.Utils.T__'215'__428
        T_Hints_146
        (MAlonzo.Code.Utils.T__'215'__428
           MAlonzo.Code.RawU.T_Untyped_208
           MAlonzo.Code.RawU.T_Untyped_208))] ->
  T_Trace_154
du_go_182 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__442 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Utils.C__'44'__442 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Utils.C__'44'__442 v6 v7
                      -> case coe v1 of
                           []
                             -> coe
                                  C_step_158 (coe v2) (coe v4) (coe v6) (coe C_done_160 (coe v7))
                           (:) v8 v9
                             -> case coe v8 of
                                  MAlonzo.Code.Utils.C__'44'__442 v10 v11
                                    -> case coe v11 of
                                         MAlonzo.Code.Utils.C__'44'__442 v12 v13
                                           -> case coe v13 of
                                                MAlonzo.Code.Utils.C__'44'__442 v14 v15
                                                  -> coe
                                                       C_step_158 (coe v2) (coe v4) (coe v6)
                                                       (coe
                                                          du_go_182
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
d_EvalResult_208 = ()
type T_EvalResult_208 = EvalResult
pattern C_success_210 a0 a1 = EvalSuccess a0 a1
pattern C_failure_212 a0 a1 a2 = EvalFailure a0 a1 a2
check_success_210 :: Integer -> Integer -> T_EvalResult_208
check_success_210 = EvalSuccess
check_failure_212 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer -> Integer -> T_EvalResult_208
check_failure_212 = EvalFailure
cover_EvalResult_208 :: EvalResult -> ()
cover_EvalResult_208 x
  = case x of
      EvalSuccess _ _ -> ()
      EvalFailure _ _ _ -> ()
