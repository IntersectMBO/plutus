{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Cardano.Constitution.Validator.Sorted (defaultConstitutionCode)
import PlutusLedgerApi.Envelope (writeCodeEnvelope)
import System.Environment (getArgs)
import System.Exit (die)

main :: IO ()
main =
  getArgs >>= \case
    [file] ->
      writeCodeEnvelope
        "*BE CAREFUL* that this is compiled from a release commit \
        \of Plutus and not from master"
        defaultConstitutionCode
        file
    _ -> die "USAGE: create-json-envelope OUT_FILE"
