module System.Environment.IgnoreAccept (ignoreAcceptOption) where

import System.Environment
import Data.List

-- | Ignores options like --accept and --accept=True from argv
ignoreAcceptOption :: IO a -> IO a
ignoreAcceptOption m = do
  args <- getArgs
  withArgs (filter (not . isPrefixOf "--accept") args) m
