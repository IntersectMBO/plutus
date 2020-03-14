module Main (main) where

import           System.Exit
import qualified Tests

main :: IO ()
main = do
  good <- and <$> sequence [Tests.runTests]
  if good then exitSuccess else exitFailure

