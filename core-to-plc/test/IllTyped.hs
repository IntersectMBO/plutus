{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS -fplugin Language.Plutus.CoreToPLC.Plugin -fplugin-opt Language.Plutus.CoreToPLC.Plugin:dont-typecheck #-}
-- the simplfiier messes with things otherwise
{-# OPTIONS_GHC   -O0 #-}

-- | Terms which currently fail the typechecker, but which should work in future.
-- In a separate file so we can give different options to the plugin.
module IllTyped where

import           Language.Plutus.CoreToPLC.Plugin
import           Language.Plutus.CoreToPLC.Primitives as Prims

blocknumPlc :: PlcCode
blocknumPlc = plc Prims.blocknum

bytestring :: PlcCode
bytestring = plc (\(x::Prims.ByteString) -> x)

verify :: PlcCode
verify = plc (\(x::Prims.ByteString) (y::Prims.ByteString) (z::Prims.ByteString) -> Prims.verifySignature x y z)

tupleMatch :: PlcCode
tupleMatch = plc (\(x:: (Int, Int)) -> let (a, b) = x in a)

-- Has a Void in it
void :: PlcCode
void = plc (\(x::Int) (y::Int) -> let a x' y' = case (x', y') of { (True, True) -> True; _ -> False; } in (x == y) `a` (y == x))
