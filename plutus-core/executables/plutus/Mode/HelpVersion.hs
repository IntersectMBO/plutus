{-# LANGUAGE TemplateHaskell #-}

module Mode.HelpVersion
    ( runHelp
    , runVersion
    ) where

import Data.Version.Extras (makeVersionInfo)
import GetOpt
import Paths_plutus_core (version)

runHelp :: IO ()
runHelp = do
    putStr $ GetOpt.usageInfo usageHeader GetOpt.optDescrs

usageHeader :: String
usageHeader = "USAGE: plutus [--compile|--run|--bench|--debug] FILES..."

runVersion :: IO ()
runVersion = putStrLn $(makeVersionInfo "plutus" version)
