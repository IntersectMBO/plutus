module Mode.HelpVersion
    ( runHelp
    , runVersion
    ) where

import GetOpt

runHelp :: IO ()
runHelp = do
    putStr $ GetOpt.usageInfo usageHeader GetOpt.optDescrs

usageHeader :: String
usageHeader = "USAGE: plutus [--compile|--run|--bench|--debug] FILES..."

runVersion :: IO ()
runVersion = putStrLn "Version 0"
