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

listConstruct :: PlcCode
listConstruct = plc ([]::[Int])

listConstruct2 :: PlcCode
listConstruct2 = plc ([1]::[Int])

listMatch :: PlcCode
listMatch = plc (\(l::[Int]) -> case l of { (x:_) -> x ; [] -> 0; })

data B a = One a | Two (B (a, a))

ptreeConstruct :: PlcCode
ptreeConstruct = plc (Two (Two (One ((1,2),(3,4)))) :: B Int)

-- TODO: replace this with 'first' when we have working recursive functions
ptreeMatch :: PlcCode
ptreeMatch = plc (\(t::B Int) -> case t of { One a -> a; Two _ -> 2; })
