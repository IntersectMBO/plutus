module Mode.HelpVersion
  ( runHelp
  , runVersion
  ) where

import Data.Version.Extras (gitAwareVersionInfo)
import GetOpt
import Paths_plutus_core qualified as Paths

runHelp :: IO ()
runHelp = do
  putStr $ GetOpt.usageInfo usageHeader GetOpt.optDescrs

usageHeader :: String
usageHeader = "USAGE: plutus [--compile|--run|--bench|--debug] FILES..."

runVersion :: IO ()
runVersion = putStrLn (gitAwareVersionInfo Paths.version)
