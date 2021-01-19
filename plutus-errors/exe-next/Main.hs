{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
module Main where

import           Data.Text.Prettyprint.Doc
import           Errors
import           Errors.TH.GenCodes

-- | Executable to help developers by returning a currently-unused error code
main :: IO ()
main =  print $
        "An error code that is not currently in-use is:"
        <+> pretty (succ $ maximum $(genCodes allErrors))
