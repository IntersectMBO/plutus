{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}

module AnyProgram.Run
  ( runRun
  ) where

import AnyProgram.Compile
import AnyProgram.IO
import AnyProgram.With
import Common
import Control.Monad
import Data.Text (unpack)
import GetOpt
import PlutusCore as PLC
import PlutusCore.Evaluation.Machine.Ck as PLC
import PlutusCore.Evaluation.Machine.ExBudget
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusPrelude
import Types
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek as UPLC

runRun
  :: (?opts :: Opts)
  => SLang s -> FromLang s -> IO ()
runRun = \case
  SPlc sN _ ->
    plcToOutName sN SName
      -- TODO: use proper errors, not unsafeFromRight
      >>> unsafeFromRight @FreeVariableError
      >>> runPlc
  SUplc sN sA ->
    withA @Typeable sA $
      uplcToOutName sN SNamedDeBruijn
        -- TODO: use proper errors, not unsafeFromRight
        >>> unsafeFromRight @FreeVariableError
        >>> runUplc
  -- we could compile pir further to plc and run that, but it feels "dishonest".
  SPir {} -> const $ failE "Cannot run a pir program."
  SData {} -> const $ failE "Cannot run data as a program."

-- TODO: add a semantic variant here to get the right machine parameters
runPlc
  :: (?opts :: Opts)
  => PLC.Program TyName Name DefaultUni DefaultFun a -> IO ()
runPlc (PLC.Program _ _ t)
  | Nothing <- _budget ?opts =
      -- CK machine currently only works with ann==() , so we void before
      case PLC.runCk defaultBuiltinsRuntimeForTesting def False (void t) of
        (Left errorWithCause, logs) -> do
          for_ logs (printE . unpack)
          failE $ show errorWithCause
        (Right finalTerm, logs) -> do
          for_ logs (printE . unpack)
          printE "Execution succeeded. Final Term:"
          -- TODO: lift the final term back to the target singleton
          printE "Execution succeeded. Final Term:"
          printE $ show $ prettyWithStyle (_prettyStyle ?opts) finalTerm
  | otherwise = failE "Budget limiting/accounting is not possible for TPLC."

-- TODO: add a semantic variant here to get the right machine parameters
runUplc
  :: (?opts :: Opts, Typeable a)
  => UPLC.UnrestrictedProgram NamedDeBruijn DefaultUni DefaultFun a -> IO ()
runUplc (UPLC.UnrestrictedProgram (UPLC.Program _ _ t)) =
  case (\(UPLC.CekReport res cost logs) -> (UPLC.cekResultToEither res, cost, logs)) $
    UPLC.runCekDeBruijn defaultCekParametersForTesting exBudgetMode logEmitter t of
    (Left errorWithCause, _, logs) -> do
      for_ logs (printE . unpack)
      failE $ show errorWithCause
    (Right finalTerm, finalBudget, logs) -> do
      for_ logs (printE . unpack)
      -- TODO: lift the final term back to the target singleton
      printE "Execution succeeded. Final Term:"
      printE $ show $ prettyWithStyle (_prettyStyle ?opts) finalTerm
      case _budget ?opts of
        Nothing -> printE $ "Used budget: " <> show finalBudget
        Just startBudget -> do
          printE $ "Remaining budget: " <> show finalBudget
          printE $ "Used budget: " <> show (startBudget `minusExBudget` finalBudget)
  where
    -- if user provided `--budget` the mode is restricting; otherwise just counting
    exBudgetMode = case _budget ?opts of
      Just budgetLimit -> coerceMode $ restricting $ ExRestrictingBudget budgetLimit
      _ -> coerceMode counting

    -- this gets rid of the CountingSt/RestrictingSt newtype wrappers
    -- See Note [Budgeting implementation for the debugger]
    coerceMode
      :: Coercible cost ExBudget
      => ExBudgetMode cost DefaultUni DefaultFun
      -> ExBudgetMode ExBudget DefaultUni DefaultFun
    coerceMode = coerce
