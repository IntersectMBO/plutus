{-# LANGUAGE ImplicitParams #-}

module Common
  ( printE
  , printED
  , failE
  ) where

import GetOpt
import Types

import Control.Monad
import System.Exit
import System.IO

printE
  :: (?opts :: Opts)
  => String -> IO ()
printE = when (_verbosity ?opts /= VQuiet) . hPutStrLn stderr

printED
  :: (?opts :: Opts)
  => String -> IO ()
printED = when (_verbosity ?opts == VDebug) . hPutStrLn stderr

-- similar to fail , just no wrap it with the text "user error"
failE
  :: (?opts :: Opts)
  => String -> IO b
failE a = do
  printE a
  exitFailure
