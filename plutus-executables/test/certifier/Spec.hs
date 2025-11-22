{-| The tests in this file run tests of the uplc certifier. Various
    unoptimised UPLC is fed to the optimiser with the certifier turned
    on, which will then call the Agda decision procedures for each of
    the phases. -}
module Main (main) where

import GHC.IO.Encoding (setLocaleEncoding, utf8)
import Test.Tasty

import Test.Certifier.Executable (executableTests)

main :: IO ()
main = do
  setLocaleEncoding utf8
  defaultMain $
    testGroup
      "Certification"
      [ executableTests
      ]
