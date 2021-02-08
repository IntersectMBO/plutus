module Main where

import           Data.ByteString.Lazy (getContents)
import           Lambda
import           ParserL
import           Prelude              hiding (getContents)

main :: IO ()
main
  = getContents >>=
      \ b ->
        case parse b of
          Nothing -> putStrLn "parse error"
          Just t -> case stepper (S . S . S $ Z) t of
            Just t' -> putStrLn . pretty $ t'
            Nothing -> putStrLn "runtime error"
{-        maybe (putStrLn "parse error") (putStrLn . pretty . Val . eval)
          (parseExp b)
-}
