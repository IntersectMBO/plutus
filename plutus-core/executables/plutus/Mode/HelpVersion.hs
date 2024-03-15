module Mode.HelpVersion
    ( runHelp
    , runVersion
    ) where

import GetOpt

runHelp :: IO ()
runHelp = do
    putStr $ GetOpt.usageInfo usageHeader GetOpt.optDescrs
    putStr usageFooter

usageHeader :: String
usageHeader =
    "USAGE: plutus [FILES...] [-o FILE | --stdout] [--pretty|--run|--bench|--debug]"

usageFooter :: String
usageFooter =
    "EXAMPLES: FIXME \n"


runVersion :: IO ()
runVersion = putStrLn "Version 0"
