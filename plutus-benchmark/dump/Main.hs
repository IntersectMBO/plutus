module Main where

import Data.ByteString qualified as B
import Data.ByteString.Short qualified as SBS

-- import PlutusBenchmark.Marlowe.Scripts.Semantics

import PlutusBenchmark.Lists.Sum.HandWritten
import PlutusCore.Default
import PlutusCore.Flat
import PlutusCore.FlatInstances
import PlutusCore.Pretty
import PlutusCore.Version
import PlutusLedgerApi.Common (serialiseCompiledCode)
import Script
import UntypedPlutusCore

main :: IO ()
main = do
  -- putStrLn $ render $ prettyReadableSimple $
  --  Program () plcVersion100 $ nested2 3

  B.writeFile "nested-0-arg-100k.flat" $
    flat $
      UnrestrictedProgram $
        nested0 100000

  B.writeFile "nested-0-arg-300k.flat" $
    flat $
      UnrestrictedProgram $
        nested0 300000

  B.writeFile "nested-0-arg-500k.flat" $
    flat $
      UnrestrictedProgram $
        nested0 500000

  B.writeFile "nested-1-arg-30k.flat" $
    flat $
      UnrestrictedProgram $
        nested1 30000

  B.writeFile "nested-1-arg-60k.flat" $
    flat $
      UnrestrictedProgram $
        nested1 60000

  B.writeFile "nested-1-arg-90k.flat" $
    flat $
      UnrestrictedProgram $
        nested1 90000

  B.writeFile "nested-2-arg-30k.flat" $
    flat $
      UnrestrictedProgram $
        nested2 30000

  B.writeFile "nested-2-arg-60k.flat" $
    flat $
      UnrestrictedProgram $
        nested2 60000

  B.writeFile "nested-2-arg-90k.flat" $
    flat $
      UnrestrictedProgram $
        nested2 90000

-- main :: IO ()
-- main = do
--   let cc = marloweValidator
--       name = "marlowe.uplc"
--       bytes = SBS.fromShort $ serialiseCompiledCode cc
--   B.writeFile name bytes
