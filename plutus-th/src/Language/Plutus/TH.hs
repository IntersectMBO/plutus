{-# LANGUAGE TemplateHaskell #-}
module Language.Plutus.TH (plutus, plutusT, PlcCode, getSerializedCode, getAst) where

import           Language.Plutus.CoreToPLC.Plugin

import           Language.Haskell.TH

-- | Covert a quoted Haskell expression into a corresponding Plutus Core program. Produces an expression of type
-- 'PlcCode'.
plutus :: Q Exp -> Q Exp
-- We would like to do `addCorePlugin "Language.Plutus.CoreToPLC.Plugin"``, but this needs template-haskell-2.13.0.0,
-- which is in the next LTS snapshot.
plutus e = [| plc $(e) |]

-- | Covert a (typed) quoted Haskell expression into a corresponding Plutus Core program.
plutusT :: Q (TExp a) -> Q (TExp PlcCode)
-- We would like to do `addCorePlugin "Language.Plutus.CoreToPLC.Plugin"``, but this needs template-haskell-2.13.0.0,
-- which is in the next LTS snapshot.
plutusT e = [||plc $$(e)||]
