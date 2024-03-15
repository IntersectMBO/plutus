{-# LANGUAGE OverloadedStrings #-}
module Mode.Compile
    ( runCompile
    ) where

import Types
import GetOpt
import AnyProgram.IO
import AnyProgram.Apply
import AnyProgram.Compile
import AnyProgram.With
import Common
import Data.Foldable

import PlutusPrelude
import Control.Monad
import Prettyprinter

runCompile :: (?opts :: Opts) => IO SomeAst
runCompile = case ?opts of
    Opts {_inputs = []} -> failE "No input file given. Use --stdin if you want to read program from stdin. See also --help"
    Opts {_output = Nothing} -> failE "No output file given. Use --stdout to write program to stdout"
    Opts {_inputs = (hd:tl), _output = Just (SomeFile sngT fileT)} -> do
        hdT <- readCompile hd sngT
        astT <- foldlM (readCompileApply sngT) hdT tl
        writeProgram sngT fileT astT
        pure $ SomeAst sngT astT

readCompileApply :: (?opts :: Opts)
                 => SLang t -> FromLang t -> SomeFile -> IO (FromLang t)
readCompileApply sngT accT someFileS = do
    astT <- readCompile someFileS sngT
    case accT `applyTarget` astT of
        -- application errors use the annotation type of the target
        Left err -> withPrettyA (_sann sngT) $ failE $ show err
        Right applied -> pure applied
  where
    applyTarget = applyProgram sngT

readCompile :: (?opts :: Opts)
            => SomeFile -> SLang t -> IO (FromLang t)
readCompile (SomeFile sngS fileS) sngT = do
    when (_verbosity ?opts == VFull) $
           printE $ show $ "Compiling" <+> pretty fileS
    astS <- readProgram sngS fileS
    case compileProgram sngS sngT astS of
        -- compilation errors use the annotation type of the sources
        Left err -> withPrettyA (_sann sngS) $ failE $ show err
        Right res -> pure res

