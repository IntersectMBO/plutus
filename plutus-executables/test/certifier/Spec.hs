{-# LANGUAGE ViewPatterns #-}

{-| The tests in this file run tests of the uplc certifier. Various
    unoptimised UPLC is fed to the optimiser with the certifier turned
    on, which will then call the Agda decision procedures for each of
    the phases. -}
module Main (main) where

import PlutusCore.Executable.Common

import Data.Maybe
import Data.Text qualified as T
import GHC.IO.Encoding (setLocaleEncoding, utf8)

import Test.Certifier.Executable (executableTests)
import Test.Tasty

main :: IO ()
main = do
  setLocaleEncoding utf8
  examples <-
    mapMaybe
      ( \(T.unpack -> name, example) -> case example of
          SomeTypedExample _ -> Nothing
          SomeUntypedExample (SomeUntypedTermExample (UntypedTermExample term)) ->
            Just (name, term)
      )
      <$> getUplcExamples
  defaultMain $
    testGroup
      "Certification"
      [ executableTests examples
      ]
