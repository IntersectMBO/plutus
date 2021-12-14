-- |
-- Module      : Foundation.IO.Terminal
-- License     : BSD-style
-- Maintainer  : Foundation
-- Stability   : experimental
-- Portability : portable
--
module Foundation.IO.Terminal
    ( putStrLn
    , putStr
    , stdin
    , stdout
    , getArgs
    , exitFailure
    , exitSuccess
    ) where

import           Basement.Imports
import qualified Prelude
import           System.IO (stdin, stdout)
import           System.Exit
import qualified System.Environment as SE (getArgs)

-- | Print a string to standard output
putStr :: String -> IO ()
putStr = Prelude.putStr . toList

-- | Print a string with a newline to standard output
putStrLn :: String -> IO ()
putStrLn = Prelude.putStrLn . toList

-- | Get the arguments from the terminal command
getArgs :: IO [String]
getArgs = fmap fromList <$> SE.getArgs
