{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}

module Mode.Compile
  ( runCompile
  ) where

import AnyProgram.Apply
import AnyProgram.Bench
import AnyProgram.Compile
import AnyProgram.Debug
import AnyProgram.IO
import AnyProgram.Run
import AnyProgram.With
import Common
import GetOpt
import Types

import Data.Foldable
import PlutusPrelude
import Prettyprinter
import System.Exit

runCompile
  :: (?opts :: Opts)
  => AfterCompile -> IO ()
runCompile afterCompile = case ?opts of
  Opts {_inputs = []} ->
    failE "No input given. Use --stdin if you want to read program from stdin. See also --help"
  Opts {_inputs = hdS : tlS, _target = SomeFile sngT fileT} -> do
    -- compile the head targetting sngT
    hdT <- readCompile sngT hdS
    -- compile the tail targetting sngT, and fold-apply the results together with the head
    astT <- foldlM (readCompileApply sngT) hdT tlS

    appliedAstT <-
      if _wholeOpt ?opts
        then -- self-compile one last time for optimisation (also runs the checks)
          compile sngT sngT astT
        else -- The checks should run also at the whole (applied) program
          check sngT astT

    writeProgram sngT appliedAstT fileT afterCompile

    case afterCompile of
      Exit {} -> exitSuccess -- nothing left to do
      Run {} -> runRun sngT appliedAstT
      Bench {} -> runBench sngT appliedAstT
      Debug {} -> runDebug sngT appliedAstT

readCompileApply
  :: (?opts :: Opts)
  => SLang t -> FromLang t -> SomeFile -> IO (FromLang t)
readCompileApply sngT accT someFileS = do
  astT <- readCompile sngT someFileS
  case accT `applyTarget` astT of
    -- application errors use the annotation type of the target
    Left err -> withA @Pretty (_sann sngT) $ failE $ show err
    Right applied -> pure applied
  where
    applyTarget = applyProgram sngT

readCompile
  :: (?opts :: Opts)
  => SLang t -> SomeFile -> IO (FromLang t)
readCompile sngT (SomeFile sngS fileS) = do
  printED $ show $ "Compiling" <+> pretty fileS
  astS <- readProgram sngS fileS
  compile sngS sngT astS

compile
  :: (?opts :: Opts)
  => SLang s -> SLang t -> FromLang s -> IO (FromLang t)
compile sngS sngT astS =
  case compileProgram sngS sngT astS of
    -- compilation errors use the annotation type of the sources
    Left err -> withA @Pretty (_sann sngS) $ failE $ show err
    Right res -> pure res

check
  :: (?opts :: Opts)
  => SLang t -> FromLang t -> IO (FromLang t)
check sngT astT =
  if length (_inputs ?opts) == 1
    -- optimization: no need to do more checks if there was no application involved
    then pure astT
    else case checkProgram sngT astT of
      -- compilation errors use the annotation type of the sources
      Left err -> do
        printE "Failed to typecheck fully-applied program. The error was:"
        withA @Pretty (_sann sngT) $ failE $ show err
      -- passed the checks, return it
      _ -> pure astT
