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

module MAlonzo.Code.Evaluator.Program where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Algorithmic
import qualified MAlonzo.Code.Algorithmic.CEK
import qualified MAlonzo.Code.Algorithmic.CK
import qualified MAlonzo.Code.Algorithmic.Erasure
import qualified MAlonzo.Code.Algorithmic.Evaluation
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Check
import qualified MAlonzo.Code.Cost
import qualified MAlonzo.Code.Cost.Base
import qualified MAlonzo.Code.Cost.Model
import qualified MAlonzo.Code.Cost.Raw
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Evaluator.Base
import qualified MAlonzo.Code.Raw
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Scoped
import qualified MAlonzo.Code.Scoped.Extrication
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.CEK
import qualified MAlonzo.Code.Untyped.CEKWithCost
import qualified MAlonzo.Code.Utils

import PlutusCore.Executable.Common
import PlutusCore.Executable.Parsers
import PlutusCore.DeBruijn
import qualified UntypedPlutusCore as U
import qualified UntypedPlutusCore.Parser as U
import qualified FFI.Untyped as U
import Raw
import PlutusCore
import Data.Bifunctor
import Data.Functor
import Data.Either
import Control.Monad.Trans.Except
import FFI.Opts
-- Evaluator.Program.Format
type T_Format_14 = Format
d_Format_14
  = error
      "MAlonzo Runtime Error: postulate evaluated: Evaluator.Program.Format"
-- Evaluator.Program.Input
type T_Input_16 = Input
d_Input_16
  = error
      "MAlonzo Runtime Error: postulate evaluated: Evaluator.Program.Input"
-- Evaluator.Program.ProgramN
type T_ProgramN_18 =
  PlutusCore.Program TyName Name DefaultUni DefaultFun PlutusCore.SrcSpan
d_ProgramN_18
  = error
      "MAlonzo Runtime Error: postulate evaluated: Evaluator.Program.ProgramN"
-- Evaluator.Program.Program
type T_Program_20 =
  PlutusCore.Program NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun ()
d_Program_20
  = error
      "MAlonzo Runtime Error: postulate evaluated: Evaluator.Program.Program"
-- Evaluator.Program.convP
d_convP_22 :: T_Program_20 -> MAlonzo.Code.Raw.T_RawTm_32
d_convP_22 = convP
-- Evaluator.Program.deBruijnify
d_deBruijnify_24 ::
  T_ProgramN_18 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_FreeVariableError_574 T_Program_20
d_deBruijnify_24
  = \ (Program ann ver tm) -> second (void . Program ann ver) . runExcept $ deBruijnTerm tm
-- Evaluator.Program.ProgramNU
type T_ProgramNU_26 =
  U.Program Name DefaultUni DefaultFun PlutusCore.SrcSpan
d_ProgramNU_26
  = error
      "MAlonzo Runtime Error: postulate evaluated: Evaluator.Program.ProgramNU"
-- Evaluator.Program.ProgramU
type T_ProgramU_28 =
  U.Program NamedDeBruijn DefaultUni DefaultFun ()
d_ProgramU_28
  = error
      "MAlonzo Runtime Error: postulate evaluated: Evaluator.Program.ProgramU"
-- Evaluator.Program.deBruijnifyU
d_deBruijnifyU_30 ::
  T_ProgramNU_26 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_FreeVariableError_574 T_ProgramU_28
d_deBruijnifyU_30
  = \ (U.Program ann ver tm) -> second (void . U.Program ann ver) . runExcept $ U.deBruijnTerm tm
-- Evaluator.Program.convPU
d_convPU_32 :: T_ProgramU_28 -> MAlonzo.Code.RawU.T_Untyped_208
d_convPU_32 = U.convP
-- Evaluator.Program.BudgetMode
d_BudgetMode_36 a0 = ()
type T_BudgetMode_36 a0 = BudgetMode a0
pattern C_Silent_40 = Silent
pattern C_Counting_42 a0 = Counting a0
pattern C_Tallying_44 a0 = Tallying a0
check_Silent_40 :: forall xA. T_BudgetMode_36 xA
check_Silent_40 = Silent
check_Counting_42 :: forall xA. xA -> T_BudgetMode_36 xA
check_Counting_42 = Counting
check_Tallying_44 :: forall xA. xA -> T_BudgetMode_36 xA
check_Tallying_44 = Tallying
cover_BudgetMode_36 :: BudgetMode a1 -> ()
cover_BudgetMode_36 x
  = case x of
      Silent -> ()
      Counting _ -> ()
      Tallying _ -> ()
-- Evaluator.Program.EvalMode
d_EvalMode_46 = ()
type T_EvalMode_46 = EvalMode
pattern C_U_48 = U
pattern C_TL_50 = TL
pattern C_TCK_52 = TCK
pattern C_TCEK_54 = TCEK
check_U_48 :: T_EvalMode_46
check_U_48 = U
check_TL_50 :: T_EvalMode_46
check_TL_50 = TL
check_TCK_52 :: T_EvalMode_46
check_TCK_52 = TCK
check_TCEK_54 :: T_EvalMode_46
check_TCEK_54 = TCEK
cover_EvalMode_46 :: EvalMode -> ()
cover_EvalMode_46 x
  = case x of
      U -> ()
      TL -> ()
      TCK -> ()
      TCEK -> ()
-- Evaluator.Program.parsePLC
d_parsePLC_56 ::
  T_ProgramN_18 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Scoped.T_ScopedTm_522
d_parsePLC_56 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42
      (coe
         MAlonzo.Code.Utils.du_withE_282
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.Evaluator.Base.C_scopeError_18
                 (coe MAlonzo.Code.Scoped.C_freeVariableError_580 (coe v1))))
         (coe d_deBruijnify_24 v0))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_withE_282
              (coe MAlonzo.Code.Evaluator.Base.C_scopeError_18)
              (coe
                 MAlonzo.Code.Scoped.d_scopeCheckTm_686 (coe (0 :: Integer))
                 (coe MAlonzo.Code.Scoped.C_Z_44)
                 (coe
                    MAlonzo.Code.Scoped.d_shifter_272 (coe (0 :: Integer))
                    (coe MAlonzo.Code.Scoped.C_Z_44) (coe d_convP_22 v1)))))
-- Evaluator.Program.parseUPLC
d_parseUPLC_62 ::
  T_ProgramNU_26 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Untyped.T__'8866'_14
d_parseUPLC_62 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42
      (coe
         MAlonzo.Code.Utils.du_withE_282
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.Evaluator.Base.C_scopeError_18
                 (coe MAlonzo.Code.Scoped.C_freeVariableError_580 (coe v1))))
         (coe d_deBruijnifyU_30 v0))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_withE_282
              (coe MAlonzo.Code.Evaluator.Base.C_scopeError_18)
              (coe
                 MAlonzo.Code.Untyped.d_scopeCheckU0_326 (coe d_convPU_32 v1))))
-- Evaluator.Program.typeCheckPLC
d_typeCheckPLC_70 ::
  MAlonzo.Code.Scoped.T_ScopedTm_522 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Check.T_TypeError_12
    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_typeCheckPLC_70 v0
  = coe
      MAlonzo.Code.Check.d_inferType_1156
      (coe MAlonzo.Code.Type.C_'8709'_4)
      (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v0)
-- Evaluator.Program.checkError
d_checkError_76 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Algorithmic.T__'8866'__178
d_checkError_76 ~v0 v1 = du_checkError_76 v1
du_checkError_76 ::
  MAlonzo.Code.Algorithmic.T__'8866'__178 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Algorithmic.T__'8866'__178
du_checkError_76 v0
  = let v1 = coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe v0) in
    coe
      (case coe v0 of
         MAlonzo.Code.Algorithmic.C_error_268
           -> coe
                MAlonzo.Code.Utils.C_inj'8321'_12
                (coe
                   MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                   (coe MAlonzo.Code.Utils.C_userError_352))
         _ -> coe v1)
-- Evaluator.Program.executePLC
d_executePLC_80 ::
  T_EvalMode_46 ->
  MAlonzo.Code.Scoped.T_ScopedTm_522 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Agda.Builtin.String.T_String_6
d_executePLC_80 v0 v1
  = case coe v0 of
      C_U_48
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe
                MAlonzo.Code.Utils.du_withE_282
                (coe
                   (\ v2 ->
                      coe
                        MAlonzo.Code.Evaluator.Base.C_typeError_14
                        (coe MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24 (coe v2))))
                (coe d_typeCheckPLC_70 (coe v1)))
             (coe
                (\ v2 ->
                   case coe v2 of
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                       -> coe
                            MAlonzo.Code.Utils.du_eitherBind_42
                            (coe
                               MAlonzo.Code.Utils.du_withE_282
                               (coe MAlonzo.Code.Evaluator.Base.C_runtimeError_20)
                               (coe
                                  MAlonzo.Code.Untyped.CEK.d_stepper_1276
                                  (coe MAlonzo.Code.Evaluator.Base.d_maxsteps_72)
                                  (coe
                                     MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222
                                     (coe MAlonzo.Code.Untyped.CEK.C_ε_10)
                                     (coe MAlonzo.Code.Untyped.CEK.C_'91''93'_18)
                                     (MAlonzo.Code.Algorithmic.Erasure.d_erase_48
                                        (coe MAlonzo.Code.Type.C_'8709'_4)
                                        (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v3)
                                        (coe v4)))))
                            (coe
                               (\ v5 ->
                                  let v6
                                        = coe
                                            MAlonzo.Code.Utils.C_inj'8321'_12
                                            (coe
                                               MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                                               (coe MAlonzo.Code.Utils.C_gasError_350)) in
                                  coe
                                    (case coe v5 of
                                       MAlonzo.Code.Untyped.CEK.C_'9633'_226 v7
                                         -> coe
                                              MAlonzo.Code.Utils.C_inj'8322'_14
                                              (coe
                                                 MAlonzo.Code.Evaluator.Base.d_prettyPrintUTm_10
                                                 (MAlonzo.Code.Untyped.d_extricateU0_240
                                                    (coe
                                                       MAlonzo.Code.Untyped.CEK.d_discharge_126
                                                       (coe v7))))
                                       MAlonzo.Code.Untyped.CEK.C_'9670'_228
                                         -> coe
                                              MAlonzo.Code.Utils.C_inj'8321'_12
                                              (coe
                                                 MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                                                 (coe MAlonzo.Code.Utils.C_userError_352))
                                       _ -> coe v6)))
                     _ -> MAlonzo.RTE.mazUnreachableError))
      C_TL_50
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe
                MAlonzo.Code.Utils.du_withE_282
                (coe
                   (\ v2 ->
                      coe
                        MAlonzo.Code.Evaluator.Base.C_typeError_14
                        (coe MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24 (coe v2))))
                (coe d_typeCheckPLC_70 (coe v1)))
             (coe
                (\ v2 ->
                   case coe v2 of
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                       -> coe
                            MAlonzo.Code.Utils.du_eitherBind_42
                            (coe
                               MAlonzo.Code.Utils.du_eitherBind_42
                               (coe
                                  MAlonzo.Code.Utils.du_withE_282
                                  (coe MAlonzo.Code.Evaluator.Base.C_runtimeError_20)
                                  (coe
                                     MAlonzo.Code.Algorithmic.Evaluation.d_stepper_86 (coe v3)
                                     (coe v4) (coe MAlonzo.Code.Evaluator.Base.d_maxsteps_72)))
                               (coe du_checkError_76))
                            (coe
                               (\ v5 ->
                                  coe
                                    MAlonzo.Code.Utils.C_inj'8322'_14
                                    (coe
                                       MAlonzo.Code.Evaluator.Base.d_prettyPrintTm_6
                                       (MAlonzo.Code.Scoped.d_unshifter_434
                                          (coe (0 :: Integer)) (coe MAlonzo.Code.Scoped.C_Z_44)
                                          (coe
                                             MAlonzo.Code.Scoped.d_extricateScope_828
                                             (coe
                                                MAlonzo.Code.Scoped.Extrication.d_len'8902'_4
                                                (coe MAlonzo.Code.Type.C_'8709'_4))
                                             (coe
                                                MAlonzo.Code.Scoped.Extrication.d_len_94
                                                (coe MAlonzo.Code.Type.C_'8709'_4)
                                                (coe MAlonzo.Code.Algorithmic.C_'8709'_4))
                                             (coe
                                                MAlonzo.Code.Scoped.Extrication.d_extricate_140
                                                (coe MAlonzo.Code.Type.C_'8709'_4)
                                                (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v3)
                                                (coe v5)))))))
                     _ -> MAlonzo.RTE.mazUnreachableError))
      C_TCK_52
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe
                MAlonzo.Code.Utils.du_withE_282
                (coe
                   (\ v2 ->
                      coe
                        MAlonzo.Code.Evaluator.Base.C_typeError_14
                        (coe MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24 (coe v2))))
                (coe d_typeCheckPLC_70 (coe v1)))
             (coe
                (\ v2 ->
                   case coe v2 of
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                       -> coe
                            MAlonzo.Code.Utils.du_eitherBind_42
                            (coe
                               MAlonzo.Code.Utils.du_withE_282
                               (coe MAlonzo.Code.Evaluator.Base.C_runtimeError_20)
                               (coe
                                  MAlonzo.Code.Algorithmic.CK.du_stepper_372
                                  (coe MAlonzo.Code.Evaluator.Base.d_maxsteps_72)
                                  (coe
                                     MAlonzo.Code.Algorithmic.CK.C__'9659'__40 (coe v3)
                                     (coe MAlonzo.Code.Algorithmic.CK.C_ε_22) (coe v4))))
                            (coe
                               (\ v5 ->
                                  let v6
                                        = coe
                                            MAlonzo.Code.Utils.C_inj'8321'_12
                                            (coe
                                               MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                                               (coe MAlonzo.Code.Utils.C_gasError_350)) in
                                  coe
                                    (case coe v5 of
                                       MAlonzo.Code.Algorithmic.CK.C_'9633'_50 v7 v8
                                         -> coe
                                              MAlonzo.Code.Utils.C_inj'8322'_14
                                              (coe
                                                 MAlonzo.Code.Evaluator.Base.d_prettyPrintTm_6
                                                 (MAlonzo.Code.Scoped.d_unshifter_434
                                                    (coe (0 :: Integer))
                                                    (coe MAlonzo.Code.Scoped.C_Z_44)
                                                    (coe
                                                       MAlonzo.Code.Scoped.d_extricateScope_828
                                                       (coe
                                                          MAlonzo.Code.Scoped.Extrication.d_len'8902'_4
                                                          (coe MAlonzo.Code.Type.C_'8709'_4))
                                                       (coe
                                                          MAlonzo.Code.Scoped.Extrication.d_len_94
                                                          (coe MAlonzo.Code.Type.C_'8709'_4)
                                                          (coe MAlonzo.Code.Algorithmic.C_'8709'_4))
                                                       (coe
                                                          MAlonzo.Code.Scoped.Extrication.d_extricate_140
                                                          (coe MAlonzo.Code.Type.C_'8709'_4)
                                                          (coe MAlonzo.Code.Algorithmic.C_'8709'_4)
                                                          (coe v3) (coe v7)))))
                                       MAlonzo.Code.Algorithmic.CK.C_'9670'_54 v7
                                         -> coe
                                              MAlonzo.Code.Utils.C_inj'8321'_12
                                              (coe
                                                 MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                                                 (coe MAlonzo.Code.Utils.C_userError_352))
                                       _ -> coe v6)))
                     _ -> MAlonzo.RTE.mazUnreachableError))
      C_TCEK_54
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe
                MAlonzo.Code.Utils.du_withE_282
                (coe
                   (\ v2 ->
                      coe
                        MAlonzo.Code.Evaluator.Base.C_typeError_14
                        (coe MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24 (coe v2))))
                (coe d_typeCheckPLC_70 (coe v1)))
             (coe
                (\ v2 ->
                   case coe v2 of
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                       -> coe
                            MAlonzo.Code.Utils.du_eitherBind_42
                            (coe
                               MAlonzo.Code.Utils.du_withE_282
                               (coe MAlonzo.Code.Evaluator.Base.C_runtimeError_20)
                               (coe
                                  MAlonzo.Code.Algorithmic.CEK.du_stepper_1602
                                  (coe MAlonzo.Code.Evaluator.Base.d_maxsteps_72)
                                  (coe
                                     MAlonzo.Code.Algorithmic.CEK.C__'894'_'9659'__1258
                                     (coe MAlonzo.Code.Algorithmic.C_'8709'_4) (coe v3)
                                     (coe MAlonzo.Code.Algorithmic.CEK.C_ε_1240)
                                     (coe MAlonzo.Code.Algorithmic.CEK.C_'91''93'_202) (coe v4))))
                            (coe
                               (\ v5 ->
                                  let v6
                                        = coe
                                            MAlonzo.Code.Utils.C_inj'8321'_12
                                            (coe
                                               MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                                               (coe MAlonzo.Code.Utils.C_gasError_350)) in
                                  coe
                                    (case coe v5 of
                                       MAlonzo.Code.Algorithmic.CEK.C_'9633'_1264 v7
                                         -> coe
                                              MAlonzo.Code.Utils.C_inj'8322'_14
                                              (coe
                                                 MAlonzo.Code.Evaluator.Base.d_prettyPrintTm_6
                                                 (MAlonzo.Code.Scoped.d_unshifter_434
                                                    (coe (0 :: Integer))
                                                    (coe MAlonzo.Code.Scoped.C_Z_44)
                                                    (coe
                                                       MAlonzo.Code.Scoped.d_extricateScope_828
                                                       (coe
                                                          MAlonzo.Code.Scoped.Extrication.d_len'8902'_4
                                                          (coe MAlonzo.Code.Type.C_'8709'_4))
                                                       (coe
                                                          MAlonzo.Code.Scoped.Extrication.d_len_94
                                                          (coe MAlonzo.Code.Type.C_'8709'_4)
                                                          (coe MAlonzo.Code.Algorithmic.C_'8709'_4))
                                                       (coe
                                                          MAlonzo.Code.Scoped.Extrication.d_extricate_140
                                                          (coe MAlonzo.Code.Type.C_'8709'_4)
                                                          (coe MAlonzo.Code.Algorithmic.C_'8709'_4)
                                                          (coe v3)
                                                          (coe
                                                             MAlonzo.Code.Algorithmic.CEK.d_discharge_228
                                                             (coe v3) (coe v7))))))
                                       MAlonzo.Code.Algorithmic.CEK.C_'9670'_1266 v7
                                         -> coe
                                              MAlonzo.Code.Utils.C_inj'8321'_12
                                              (coe
                                                 MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                                                 (coe MAlonzo.Code.Utils.C_userError_352))
                                       _ -> coe v6)))
                     _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Evaluator.Program.showUPLCResult
d_showUPLCResult_138 ::
  MAlonzo.Code.Untyped.CEK.T_State_218 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showUPLCResult_138 v0
  = let v1
          = coe
              MAlonzo.Code.Utils.C_inj'8321'_12
              (coe
                 MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                 (coe MAlonzo.Code.Utils.C_gasError_350)) in
    coe
      (case coe v0 of
         MAlonzo.Code.Untyped.CEK.C_'9633'_226 v2
           -> coe
                MAlonzo.Code.Utils.C_inj'8322'_14
                (coe
                   MAlonzo.Code.Evaluator.Base.d_prettyPrintUTm_10
                   (MAlonzo.Code.Untyped.d_extricateU0_240
                      (coe MAlonzo.Code.Untyped.CEK.d_discharge_126 (coe v2))))
         MAlonzo.Code.Untyped.CEK.C_'9670'_228
           -> coe
                MAlonzo.Code.Utils.C_inj'8321'_12
                (coe
                   MAlonzo.Code.Evaluator.Base.C_runtimeError_20
                   (coe MAlonzo.Code.Utils.C_userError_352))
         _ -> coe v1)
-- Evaluator.Program.executeUPLCwithMP
d_executeUPLCwithMP_144 ::
  () ->
  MAlonzo.Code.Utils.T__'215'__366
    MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
    (MAlonzo.Code.Utils.T_List_384
       (MAlonzo.Code.Utils.T__'215'__366
          MAlonzo.Code.Agda.Builtin.String.T_String_6
          MAlonzo.Code.Cost.Raw.T_CpuAndMemoryModel_164)) ->
  (MAlonzo.Code.Utils.T__'215'__366
     MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
     (MAlonzo.Code.Builtin.T_Builtin_2 ->
      MAlonzo.Code.Cost.Model.T_BuiltinModel_62) ->
   MAlonzo.Code.Cost.Base.T_MachineParameters_46) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Agda.Builtin.String.T_String_6
d_executeUPLCwithMP_144 ~v0 v1 v2 v3 v4
  = du_executeUPLCwithMP_144 v1 v2 v3 v4
du_executeUPLCwithMP_144 ::
  MAlonzo.Code.Utils.T__'215'__366
    MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
    (MAlonzo.Code.Utils.T_List_384
       (MAlonzo.Code.Utils.T__'215'__366
          MAlonzo.Code.Agda.Builtin.String.T_String_6
          MAlonzo.Code.Cost.Raw.T_CpuAndMemoryModel_164)) ->
  (MAlonzo.Code.Utils.T__'215'__366
     MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
     (MAlonzo.Code.Builtin.T_Builtin_2 ->
      MAlonzo.Code.Cost.Model.T_BuiltinModel_62) ->
   MAlonzo.Code.Cost.Base.T_MachineParameters_46) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.String.T_String_6) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Agda.Builtin.String.T_String_6
du_executeUPLCwithMP_144 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Utils.C__'44'__380 v4 v5
        -> let v6
                 = coe
                     MAlonzo.Code.Data.Maybe.Base.du_maybe_32
                     (coe
                        (\ v6 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                             (coe MAlonzo.Code.Cost.Model.d_lookupModel_474 (coe v6))))
                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                     (coe
                        MAlonzo.Code.Cost.Model.du_allJust_510
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                           (coe
                              MAlonzo.Code.Cost.Model.d_getModel_432
                              (coe MAlonzo.Code.Builtin.C_addInteger_4) (coe v5))
                           (coe
                              MAlonzo.Code.Data.List.Base.du_map_22
                              (coe
                                 (\ v6 -> MAlonzo.Code.Cost.Model.d_getModel_432 (coe v6) (coe v5)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                 (coe MAlonzo.Code.Builtin.C_subtractInteger_6)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                    (coe MAlonzo.Code.Builtin.C_multiplyInteger_8)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                       (coe MAlonzo.Code.Builtin.C_divideInteger_10)
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                          (coe MAlonzo.Code.Builtin.C_quotientInteger_12)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                             (coe MAlonzo.Code.Builtin.C_remainderInteger_14)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe MAlonzo.Code.Builtin.C_modInteger_16)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                   (coe MAlonzo.Code.Builtin.C_equalsInteger_18)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                      (coe
                                                         MAlonzo.Code.Builtin.C_lessThanInteger_20)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            MAlonzo.Code.Builtin.C_lessThanEqualsInteger_22)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                            (coe
                                                               MAlonzo.Code.Builtin.C_appendByteString_24)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe
                                                                  MAlonzo.Code.Builtin.C_consByteString_26)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                  (coe
                                                                     MAlonzo.Code.Builtin.C_sliceByteString_28)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                     (coe
                                                                        MAlonzo.Code.Builtin.C_lengthOfByteString_30)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe
                                                                           MAlonzo.Code.Builtin.C_indexByteString_32)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe
                                                                              MAlonzo.Code.Builtin.C_equalsByteString_34)
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                              (coe
                                                                                 MAlonzo.Code.Builtin.C_lessThanByteString_36)
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                 (coe
                                                                                    MAlonzo.Code.Builtin.C_lessThanEqualsByteString_38)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                    (coe
                                                                                       MAlonzo.Code.Builtin.C_sha2'45'256_40)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe
                                                                                          MAlonzo.Code.Builtin.C_sha3'45'256_42)
                                                                                       (coe
                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                          (coe
                                                                                             MAlonzo.Code.Builtin.C_blake2b'45'256_44)
                                                                                          (coe
                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                             (coe
                                                                                                MAlonzo.Code.Builtin.C_verifyEd25519Signature_46)
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                (coe
                                                                                                   MAlonzo.Code.Builtin.C_verifyEcdsaSecp256k1Signature_48)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Builtin.C_verifySchnorrSecp256k1Signature_50)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Builtin.C_appendString_52)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Builtin.C_equalsString_54)
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Builtin.C_encodeUtf8_56)
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Builtin.C_decodeUtf8_58)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Builtin.C_ifThenElse_60)
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Builtin.C_chooseUnit_62)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Builtin.C_trace_64)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Builtin.C_fstPair_66)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Builtin.C_sndPair_68)
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Builtin.C_chooseList_70)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Builtin.C_mkCons_72)
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Builtin.C_headList_74)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Builtin.C_tailList_76)
                                                                                                                                          (coe
                                                                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Builtin.C_nullList_78)
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Builtin.C_lengthOfArray_80)
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Builtin.C_listToArray_82)
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Builtin.C_indexArray_84)
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Builtin.C_chooseData_86)
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Builtin.C_constrData_88)
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.Builtin.C_mapData_90)
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Builtin.C_listData_92)
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                     (coe
                                                                                                                                                                        MAlonzo.Code.Builtin.C_iData_94)
                                                                                                                                                                     (coe
                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Builtin.C_bData_96)
                                                                                                                                                                        (coe
                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Builtin.C_unConstrData_98)
                                                                                                                                                                           (coe
                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                              (coe
                                                                                                                                                                                 MAlonzo.Code.Builtin.C_unMapData_100)
                                                                                                                                                                              (coe
                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                 (coe
                                                                                                                                                                                    MAlonzo.Code.Builtin.C_unListData_102)
                                                                                                                                                                                 (coe
                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                    (coe
                                                                                                                                                                                       MAlonzo.Code.Builtin.C_unIData_104)
                                                                                                                                                                                    (coe
                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                       (coe
                                                                                                                                                                                          MAlonzo.Code.Builtin.C_unBData_106)
                                                                                                                                                                                       (coe
                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                          (coe
                                                                                                                                                                                             MAlonzo.Code.Builtin.C_equalsData_108)
                                                                                                                                                                                          (coe
                                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                             (coe
                                                                                                                                                                                                MAlonzo.Code.Builtin.C_serialiseData_110)
                                                                                                                                                                                             (coe
                                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   MAlonzo.Code.Builtin.C_mkPairData_112)
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                   (coe
                                                                                                                                                                                                      MAlonzo.Code.Builtin.C_mkNilData_114)
                                                                                                                                                                                                   (coe
                                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         MAlonzo.Code.Builtin.C_mkNilPairData_116)
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'add_118)
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'neg_120)
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'scalarMul_122)
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'equal_124)
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'hashToGroup_126)
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                           MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'compress_128)
                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'uncompress_130)
                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'add_132)
                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                    MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'neg_134)
                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                       MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'scalarMul_136)
                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                          MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'equal_138)
                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                             MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'hashToGroup_140)
                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'compress_142)
                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                   MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'uncompress_144)
                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                                      MAlonzo.Code.Builtin.C_bls12'45'381'45'millerLoop_146)
                                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                         MAlonzo.Code.Builtin.C_bls12'45'381'45'mulMlResult_148)
                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                            MAlonzo.Code.Builtin.C_bls12'45'381'45'finalVerify_150)
                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                                                               MAlonzo.Code.Builtin.C_keccak'45'256_152)
                                                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                                  MAlonzo.Code.Builtin.C_blake2b'45'224_154)
                                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                     MAlonzo.Code.Builtin.C_byteStringToInteger_156)
                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                                        MAlonzo.Code.Builtin.C_integerToByteString_158)
                                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                                                           MAlonzo.Code.Builtin.C_andByteString_160)
                                                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                                                                              MAlonzo.Code.Builtin.C_orByteString_162)
                                                                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                                 MAlonzo.Code.Builtin.C_xorByteString_164)
                                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                                                    MAlonzo.Code.Builtin.C_complementByteString_166)
                                                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                                                                       MAlonzo.Code.Builtin.C_readBit_168)
                                                                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                                                                          MAlonzo.Code.Builtin.C_writeBits_170)
                                                                                                                                                                                                                                                                                       (coe
                                                                                                                                                                                                                                                                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                                                             MAlonzo.Code.Builtin.C_replicateByte_172)
                                                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                                                                MAlonzo.Code.Builtin.C_shiftByteString_174)
                                                                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                                                                   MAlonzo.Code.Builtin.C_rotateByteString_176)
                                                                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                                                                                      MAlonzo.Code.Builtin.C_countSetBits_178)
                                                                                                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                                                                                                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                                                                         MAlonzo.Code.Builtin.C_findFirstSetBit_180)
                                                                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                                                                            MAlonzo.Code.Builtin.C_ripemd'45'160_182)
                                                                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                                                                                                               MAlonzo.Code.Builtin.C_expModInteger_184)
                                                                                                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                                                                                  MAlonzo.Code.Builtin.C_dropList_186)
                                                                                                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                                                                     MAlonzo.Code.Builtin.C_bls12'45'381'45'G1'45'multiScalarMul_188)
                                                                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                                                                                        MAlonzo.Code.Builtin.C_bls12'45'381'45'G2'45'multiScalarMul_190)
                                                                                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                                                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) in
           coe
             (case coe v6 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                  -> coe
                       MAlonzo.Code.Utils.du_eitherBind_42
                       (coe
                          MAlonzo.Code.Utils.du_withE_282
                          (coe MAlonzo.Code.Evaluator.Base.C_runtimeError_20)
                          (coe
                             MAlonzo.Code.Utils.d_wrvalue_314
                             (coe
                                MAlonzo.Code.Untyped.CEKWithCost.du_stepperC_338
                                (coe v1 (coe MAlonzo.Code.Utils.C__'44'__380 (coe v4) (coe v7)))
                                (coe MAlonzo.Code.Evaluator.Base.d_maxsteps_72)
                                (coe
                                   MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222
                                   (coe MAlonzo.Code.Untyped.CEK.C_ε_10)
                                   (coe MAlonzo.Code.Untyped.CEK.C_'91''93'_18) v3))))
                       (coe
                          (\ v8 ->
                             coe
                               MAlonzo.Code.Utils.du_eitherBind_42
                               (coe d_showUPLCResult_138 (coe v8))
                               (coe
                                  (\ v9 ->
                                     coe
                                       MAlonzo.Code.Utils.C_inj'8322'_14
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20 v9
                                          (coe
                                             v2
                                             (MAlonzo.Code.Utils.d_accum_316
                                                (coe
                                                   MAlonzo.Code.Untyped.CEKWithCost.du_stepperC_338
                                                   (coe
                                                      v1
                                                      (coe
                                                         MAlonzo.Code.Utils.C__'44'__380 (coe v4)
                                                         (coe v7)))
                                                   (coe MAlonzo.Code.Evaluator.Base.d_maxsteps_72)
                                                   (coe
                                                      MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222
                                                      (coe MAlonzo.Code.Untyped.CEK.C_ε_10)
                                                      (coe MAlonzo.Code.Untyped.CEK.C_'91''93'_18)
                                                      v3)))))))))
                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                  -> coe
                       MAlonzo.Code.Utils.C_inj'8321'_12
                       (coe
                          MAlonzo.Code.Evaluator.Base.C_jsonError_22
                          (coe ("while processing parameters." :: Data.Text.Text)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Evaluator.Program.executeUPLC
d_executeUPLC_192 ::
  T_BudgetMode_36
    (MAlonzo.Code.Utils.T__'215'__366
       MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
       (MAlonzo.Code.Utils.T_List_384
          (MAlonzo.Code.Utils.T__'215'__366
             MAlonzo.Code.Agda.Builtin.String.T_String_6
             MAlonzo.Code.Cost.Raw.T_CpuAndMemoryModel_164))) ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Agda.Builtin.String.T_String_6
d_executeUPLC_192 v0 v1
  = case coe v0 of
      C_Silent_40
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe
                MAlonzo.Code.Utils.du_withE_282
                (coe MAlonzo.Code.Evaluator.Base.C_runtimeError_20)
                (coe
                   MAlonzo.Code.Untyped.CEK.d_stepper_1276
                   (coe MAlonzo.Code.Evaluator.Base.d_maxsteps_72)
                   (coe
                      MAlonzo.Code.Untyped.CEK.C__'894'_'9659'__222
                      (coe MAlonzo.Code.Untyped.CEK.C_ε_10)
                      (coe MAlonzo.Code.Untyped.CEK.C_'91''93'_18) v1)))
             (coe d_showUPLCResult_138)
      C_Counting_42 v2
        -> coe
             du_executeUPLCwithMP_144 (coe v2)
             (coe MAlonzo.Code.Cost.d_machineParameters_140)
             (coe MAlonzo.Code.Cost.d_countingReport_144) (coe v1)
      C_Tallying_44 v2
        -> coe
             du_executeUPLCwithMP_144 (coe v2)
             (coe MAlonzo.Code.Cost.d_tallyingMachineParameters_220)
             (coe MAlonzo.Code.Cost.d_tallyingReport_224) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Evaluator.Program.evalProgramNU
d_evalProgramNU_204 ::
  T_BudgetMode_36
    (MAlonzo.Code.Utils.T__'215'__366
       MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
       (MAlonzo.Code.Utils.T_List_384
          (MAlonzo.Code.Utils.T__'215'__366
             MAlonzo.Code.Agda.Builtin.String.T_String_6
             MAlonzo.Code.Cost.Raw.T_CpuAndMemoryModel_164))) ->
  T_ProgramNU_26 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Agda.Builtin.String.T_String_6
d_evalProgramNU_204 v0 v1
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42 (coe d_parseUPLC_62 (coe v1))
      (coe d_executeUPLC_192 (coe v0))
-- Evaluator.Program.evalProgramN
d_evalProgramN_212 ::
  T_EvalMode_46 ->
  T_ProgramN_18 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Agda.Builtin.String.T_String_6
d_evalProgramN_212 v0 v1
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42 (coe d_parsePLC_56 (coe v1))
      (coe d_executePLC_80 (coe v0))
-- Evaluator.Program.typeCheckProgramN
d_typeCheckProgramN_220 ::
  T_ProgramN_18 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Evaluator.Base.T_ERROR_12
    MAlonzo.Code.Agda.Builtin.String.T_String_6
d_typeCheckProgramN_220 v0
  = coe
      MAlonzo.Code.Utils.du_eitherBind_42 (coe d_parsePLC_56 (coe v0))
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.du_eitherBind_42
              (coe
                 MAlonzo.Code.Utils.du_withE_282
                 (coe
                    (\ v2 ->
                       coe
                         MAlonzo.Code.Evaluator.Base.C_typeError_14
                         (coe MAlonzo.Code.Evaluator.Base.d_uglyTypeError_24 (coe v2))))
                 (coe d_typeCheckPLC_70 (coe v1)))
              (coe
                 (\ v2 ->
                    case coe v2 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                        -> coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe
                                MAlonzo.Code.Evaluator.Base.d_prettyPrintTy_8
                                (MAlonzo.Code.Scoped.d_unshifterTy_360
                                   (coe (0 :: Integer)) (coe MAlonzo.Code.Scoped.C_Z_44)
                                   (coe
                                      MAlonzo.Code.Scoped.d_extricateScopeTy_780
                                      (coe
                                         MAlonzo.Code.Scoped.Extrication.d_len'8902'_4
                                         (coe MAlonzo.Code.Type.C_'8709'_4))
                                      (coe
                                         MAlonzo.Code.Scoped.Extrication.d_extricateNf'8902'_26
                                         (coe MAlonzo.Code.Type.C_'8709'_4)
                                         (coe MAlonzo.Code.Utils.C_'42'_654) (coe v3)))))
                      _ -> MAlonzo.RTE.mazUnreachableError))))
