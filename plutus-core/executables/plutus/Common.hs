module Common
    ( printE
    , failE
    ) where

import System.IO
import System.Exit

printE :: String -> IO ()
printE = hPutStrLn stderr

-- like fail , just no wrap it with the text "user error"
failE :: String -> IO b
failE a = do
    printE a
    exitFailure
