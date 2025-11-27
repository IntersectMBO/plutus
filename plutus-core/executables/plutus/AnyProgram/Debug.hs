{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}

module AnyProgram.Debug
  ( runDebug
  ) where

import Common
import Debugger.TUI.Main qualified
import GetOpt
import Types
import UntypedPlutusCore as UPLC

runDebug
  :: (?opts :: Opts)
  => SLang s -> FromLang s -> IO ()
runDebug = \case
  SUplc sn sa -> Debugger.TUI.Main.main sn sa . UPLC.unUnrestrictedProgram
  _ -> const $ failE "Debugging pir/tplc program is not available."
