module Main where

import           System.Exit        (exitFailure)
import           System.Process

import qualified MAlonzo.Code.Main  as M

import           System.Environment

tests = ["succInteger","unitval","true","false","churchZero","churchSucc","overapplication","factorial","fibonacci","NatRoundTrip","ListSum","IfIntegers","ApplyAdd1","ApplyAdd2"]

runTest :: String -> IO [()]
runTest test = do
  example <- readProcess "plc" ["example","-s",test] []
  writeFile "tmp" example
  withArgs ["evaluate","--file","tmp"]  M.main


main = sequence (map runTest tests)
