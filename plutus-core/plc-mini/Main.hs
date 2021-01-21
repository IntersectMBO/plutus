module Main where

import           Lang

import           Parser

import           Prelude              hiding (getContents)

import           Data.ByteString.Lazy (getContents)

main :: IO ()
main
  = getContents >>=
      \ b ->
        maybe (putStrLn "parse error")
          (\ e ->
             putStrLn (showsPrec 0 e "") >>
               putStrLn (showsPrec 0 (eval (\ _ -> 0) e) ""))
          (parse b)

