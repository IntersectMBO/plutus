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
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Utils

import UntypedPlutusCore.Transform.Simplifier
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
-- VerifiedCompilation.Trace.Trace
d_Trace_22 a0 = ()
data T_Trace_22
  = C_step_26 T_SimplifierTag_4 AgdaAny T_Trace_22 |
    C_done_28 AgdaAny
-- VerifiedCompilation.Trace.head
d_head_32 :: T_Trace_22 -> AgdaAny
d_head_32 v0
  = case coe v0 of
      C_step_26 v1 v2 v3 -> coe v2
      C_done_28 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace.Dump
d_Dump_38 :: ()
d_Dump_38 = erased
-- VerifiedCompilation.Trace.toTrace
d_toTrace_40 ::
  MAlonzo.Code.Utils.T_List_432
    (MAlonzo.Code.Utils.T__'215'__414
       T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__414
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  Maybe T_Trace_22
d_toTrace_40 v0
  = case coe v0 of
      MAlonzo.Code.Utils.C_'91''93'_436
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Utils.C__'8759'__438 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe du_go_50 (coe v1) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- VerifiedCompilation.Trace._.go
d_go_50 ::
  MAlonzo.Code.Utils.T__'215'__414
    T_SimplifierTag_4
    (MAlonzo.Code.Utils.T__'215'__414
       MAlonzo.Code.RawU.T_Untyped_208 MAlonzo.Code.RawU.T_Untyped_208) ->
  MAlonzo.Code.Utils.T_List_432
    (MAlonzo.Code.Utils.T__'215'__414
       T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__414
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  MAlonzo.Code.Utils.T__'215'__414
    T_SimplifierTag_4
    (MAlonzo.Code.Utils.T__'215'__414
       MAlonzo.Code.RawU.T_Untyped_208 MAlonzo.Code.RawU.T_Untyped_208) ->
  MAlonzo.Code.Utils.T_List_432
    (MAlonzo.Code.Utils.T__'215'__414
       T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__414
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  T_Trace_22
d_go_50 ~v0 ~v1 v2 v3 = du_go_50 v2 v3
du_go_50 ::
  MAlonzo.Code.Utils.T__'215'__414
    T_SimplifierTag_4
    (MAlonzo.Code.Utils.T__'215'__414
       MAlonzo.Code.RawU.T_Untyped_208 MAlonzo.Code.RawU.T_Untyped_208) ->
  MAlonzo.Code.Utils.T_List_432
    (MAlonzo.Code.Utils.T__'215'__414
       T_SimplifierTag_4
       (MAlonzo.Code.Utils.T__'215'__414
          MAlonzo.Code.RawU.T_Untyped_208
          MAlonzo.Code.RawU.T_Untyped_208)) ->
  T_Trace_22
du_go_50 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__428 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Utils.C__'44'__428 v4 v5
               -> case coe v1 of
                    MAlonzo.Code.Utils.C_'91''93'_436
                      -> coe C_step_26 (coe v2) (coe v4) (coe C_done_28 (coe v5))
                    MAlonzo.Code.Utils.C__'8759'__438 v6 v7
                      -> case coe v6 of
                           MAlonzo.Code.Utils.C__'44'__428 v8 v9
                             -> case coe v9 of
                                  MAlonzo.Code.Utils.C__'44'__428 v10 v11
                                    -> coe
                                         C_step_26 (coe v2) (coe v4)
                                         (coe
                                            du_go_50
                                            (coe
                                               MAlonzo.Code.Utils.C__'44'__428 (coe v8)
                                               (coe
                                                  MAlonzo.Code.Utils.C__'44'__428 (coe v5)
                                                  (coe v11)))
                                            (coe v7))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
