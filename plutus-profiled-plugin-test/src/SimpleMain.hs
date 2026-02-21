{-# OPTIONS -fplugin SimplePlugin -fplugin-opt SimplePlugin:test #-}

module SimpleMain where

main :: IO ()
main = putStrLn "Hello, Haskell!"