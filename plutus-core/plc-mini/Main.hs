module Main where

import           Lang

import           Parser

import           Prelude              hiding (getContents)

import           Data.ByteString.Lazy (getContents)

main :: IO ()
main
  = getContents >>=
      \ b ->
        maybe (putStrLn "parse error") (putStrLn . pretty . Val . eval)
          (parse b)

