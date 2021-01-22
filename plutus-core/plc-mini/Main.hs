module Main where

import           Data.ByteString.Lazy (getContents)
import           Lang
import           Parser
import           Prelude              hiding (getContents)

main :: IO ()
main
  = getContents >>=
      \ b ->
        maybe (putStrLn "parse error") (putStrLn . pretty . Val . eval)
          (parse b)

