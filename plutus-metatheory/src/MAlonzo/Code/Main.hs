{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Main where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.IO qualified
import MAlonzo.Code.Agda.Builtin.String qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Cost.Raw qualified
import MAlonzo.Code.Evaluator.Base qualified
import MAlonzo.Code.Evaluator.Program qualified
import MAlonzo.Code.IO.Primitive.Core qualified
import MAlonzo.Code.Utils qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

import Data.Text.IO qualified as TextIO
import FFI.Opts
import PlutusCore.Executable.Common
import PlutusCore.Executable.Parsers
import System.Exit
-- Main.putStrLn
d_putStrLn_12 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    () MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_putStrLn_12 = TextIO.putStrLn
-- Main.IOMonad
d_IOMonad_14 :: MAlonzo.Code.Utils.T_Monad_186
d_IOMonad_14
  = coe
      MAlonzo.Code.Utils.C_Monad'46'constructor_12257
      (\ v0 -> coe MAlonzo.Code.IO.Primitive.Core.du_return_16 (coe ()))
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.IO.Primitive.Core.d__'62''62''61'__14 () erased ()))
-- Main.FilePath
type T_FilePath_16 = FilePath
d_FilePath_16
  = error "MAlonzo Runtime Error: postulate evaluated: Main.FilePath"
-- Main.exitFailure
d_exitFailure_18 ::
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    () MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exitFailure_18 = exitFailure
-- Main.exitSuccess
d_exitSuccess_20 ::
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    () MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_exitSuccess_20 = exitSuccess
-- Main.EvalOptions
d_EvalOptions_24 a0 = ()
type T_EvalOptions_24 a0 = EvalOptions a0
pattern C_EvalOpts_28 a0 a1 a2 a3 = EvalOpts a0 a1 a2 a3
check_EvalOpts_28 ::
  forall xA.
    MAlonzo.Code.Evaluator.Program.T_Input_16 ->
    MAlonzo.Code.Evaluator.Program.T_Format_14 ->
    MAlonzo.Code.Evaluator.Program.T_EvalMode_46 ->
    MAlonzo.Code.Evaluator.Program.T_BudgetMode_36 xA ->
    T_EvalOptions_24 xA
check_EvalOpts_28 = EvalOpts
cover_EvalOptions_24 :: EvalOptions a1 -> ()
cover_EvalOptions_24 x
  = case x of
      EvalOpts _ _ _ _ -> ()
-- Main.TypecheckOptions
d_TypecheckOptions_30 = ()
type T_TypecheckOptions_30 = TypecheckOptions
pattern C_TCOpts_32 a0 a1 = TCOpts a0 a1
check_TCOpts_32 ::
  MAlonzo.Code.Evaluator.Program.T_Input_16 ->
  MAlonzo.Code.Evaluator.Program.T_Format_14 -> T_TypecheckOptions_30
check_TCOpts_32 = TCOpts
cover_TypecheckOptions_30 :: TypecheckOptions -> ()
cover_TypecheckOptions_30 x
  = case x of
      TCOpts _ _ -> ()
-- Main.Command
d_Command_36 a0 = ()
type T_Command_36 a0 = Command a0
pattern C_Eval_40 a0 = Eval a0
pattern C_Typecheck_42 a0 = Typecheck a0
check_Eval_40 :: forall xA. T_EvalOptions_24 xA -> T_Command_36 xA
check_Eval_40 = Eval
check_Typecheck_42 ::
  forall xA. T_TypecheckOptions_30 -> T_Command_36 xA
check_Typecheck_42 = Typecheck
cover_Command_36 :: Command a1 -> ()
cover_Command_36 x
  = case x of
      Eval _      -> ()
      Typecheck _ -> ()
-- Main.execP
d_execP_44 ::
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    ()
    (T_Command_36
       (MAlonzo.Code.Utils.T__'215'__366
          MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
          (MAlonzo.Code.Utils.T_List_384
             (MAlonzo.Code.Utils.T__'215'__366
                MAlonzo.Code.Agda.Builtin.String.T_String_6
                MAlonzo.Code.Cost.Raw.T_CpuAndMemoryModel_164))))
d_execP_44 = execP
-- Main.parse
d_parse_46 ::
  MAlonzo.Code.Evaluator.Program.T_Format_14 ->
  MAlonzo.Code.Evaluator.Program.T_Input_16 ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    () MAlonzo.Code.Evaluator.Program.T_ProgramN_18
d_parse_46 = readProgram
-- Main.parseU
d_parseU_48 ::
  MAlonzo.Code.Evaluator.Program.T_Format_14 ->
  MAlonzo.Code.Evaluator.Program.T_Input_16 ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    () MAlonzo.Code.Evaluator.Program.T_ProgramNU_26
d_parseU_48 = readProgram
-- Main.evalInput
d_evalInput_50 ::
  MAlonzo.Code.Evaluator.Program.T_EvalMode_46 ->
  MAlonzo.Code.Evaluator.Program.T_BudgetMode_36
    (MAlonzo.Code.Utils.T__'215'__366
       MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
       (MAlonzo.Code.Utils.T_List_384
          (MAlonzo.Code.Utils.T__'215'__366
             MAlonzo.Code.Agda.Builtin.String.T_String_6
             MAlonzo.Code.Cost.Raw.T_CpuAndMemoryModel_164))) ->
  MAlonzo.Code.Evaluator.Program.T_Format_14 ->
  MAlonzo.Code.Evaluator.Program.T_Input_16 ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    AgdaAny
    (MAlonzo.Code.Utils.T_Either_6
       MAlonzo.Code.Evaluator.Base.T_ERROR_12
       MAlonzo.Code.Agda.Builtin.String.T_String_6)
d_evalInput_50 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Utils.du_fmap_224 (coe d_IOMonad_14)
              (coe MAlonzo.Code.Evaluator.Program.d_evalProgramN_212 (coe v0))
              (coe d_parse_46 v2 v3) in
    coe
      (case coe v0 of
         MAlonzo.Code.Evaluator.Program.C_U_48
           -> coe
                MAlonzo.Code.Utils.du_fmap_224 (coe d_IOMonad_14)
                (coe MAlonzo.Code.Evaluator.Program.d_evalProgramNU_204 (coe v1))
                (coe d_parseU_48 v2 v3)
         _ -> coe v4)
-- Main.tcInput
d_tcInput_64 ::
  MAlonzo.Code.Evaluator.Program.T_Format_14 ->
  MAlonzo.Code.Evaluator.Program.T_Input_16 ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    AgdaAny
    (MAlonzo.Code.Utils.T_Either_6
       MAlonzo.Code.Evaluator.Base.T_ERROR_12
       MAlonzo.Code.Agda.Builtin.String.T_String_6)
d_tcInput_64 v0 v1
  = coe
      MAlonzo.Code.Utils.du_fmap_224 (coe d_IOMonad_14)
      (coe MAlonzo.Code.Evaluator.Program.d_typeCheckProgramN_220)
      (coe d_parse_46 v0 v1)
-- Main.main'
d_main''_70 ::
  T_Command_36
    (MAlonzo.Code.Utils.T__'215'__366
       MAlonzo.Code.Cost.Raw.T_HCekMachineCosts_4
       (MAlonzo.Code.Utils.T_List_384
          (MAlonzo.Code.Utils.T__'215'__366
             MAlonzo.Code.Agda.Builtin.String.T_String_6
             MAlonzo.Code.Cost.Raw.T_CpuAndMemoryModel_164))) ->
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    AgdaAny MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_main''_70 v0
  = case coe v0 of
      C_Eval_40 v1
        -> case coe v1 of
             C_EvalOpts_28 v2 v3 v4 v5
               -> coe
                    MAlonzo.Code.IO.Primitive.Core.d__'62''62''61'__14 () erased ()
                    erased (d_evalInput_50 (coe v4) (coe v5) (coe v3) (coe v2))
                    (\ v6 ->
                       case coe v6 of
                         MAlonzo.Code.Utils.C_inj'8321'_12 v7
                           -> coe
                                MAlonzo.Code.Utils.du__'62''62'__214 (coe d_IOMonad_14)
                                (coe
                                   d_putStrLn_12
                                   (MAlonzo.Code.Evaluator.Base.d_reportError_66 (coe v7)))
                                (coe d_exitFailure_18)
                         MAlonzo.Code.Utils.C_inj'8322'_14 v7
                           -> coe
                                MAlonzo.Code.Utils.du__'62''62'__214 (coe d_IOMonad_14)
                                (coe d_putStrLn_12 v7) (coe d_exitSuccess_20)
                         _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_Typecheck_42 v1
        -> case coe v1 of
             C_TCOpts_32 v2 v3
               -> coe
                    MAlonzo.Code.IO.Primitive.Core.d__'62''62''61'__14 () erased ()
                    erased (d_tcInput_64 (coe v3) (coe v2))
                    (\ v4 ->
                       case coe v4 of
                         MAlonzo.Code.Utils.C_inj'8321'_12 v5
                           -> coe
                                MAlonzo.Code.Utils.du__'62''62'__214 (coe d_IOMonad_14)
                                (coe
                                   d_putStrLn_12
                                   (MAlonzo.Code.Evaluator.Base.d_reportError_66 (coe v5)))
                                (coe d_exitFailure_18)
                         MAlonzo.Code.Utils.C_inj'8322'_14 v5
                           -> coe
                                MAlonzo.Code.Utils.du__'62''62'__214 (coe d_IOMonad_14)
                                (coe d_putStrLn_12 v5) (coe d_exitSuccess_20)
                         _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
main = coe d_main_96
-- Main.main
d_main_96 ::
  MAlonzo.Code.Agda.Builtin.IO.T_IO_8
    AgdaAny MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_main_96
  = coe
      MAlonzo.Code.IO.Primitive.Core.d__'62''62''61'__14 () erased ()
      erased d_execP_44 d_main''_70
