{-# OPTIONS_GHC -fplugin=SimplePlugin #-}

module Main where

import Control.Concurrent

main :: IO ()
main = do
  let getBool = do
        threadDelay 1000000
        return False
  b <-
    {-# SCC "YYYYYYYYYYYYYY" #-}
    getBool
  putStrLn ("I got a bool from the main module -> " ++ show b)
