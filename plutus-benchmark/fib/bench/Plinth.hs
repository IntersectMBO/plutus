{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

module Plinth (fib, fibCompiled, fibK) where

import PlutusCore qualified as PLC
import PlutusCore.Default
import PlutusTx.Builtins qualified as P
import PlutusTx.Code
import PlutusTx.Lift (liftCodeDef)
import PlutusTx.TH (compile)
import UntypedPlutusCore qualified as UPLC

type Program = UPLC.Program PLC.NamedDeBruijn DefaultUni DefaultFun ()

fib :: Integer -> Integer
fib k
  | k `P.equalsInteger` 0 = 0
  | k `P.equalsInteger` 1 = 1
  | otherwise = fib (k `P.subtractInteger` 1) `P.addInteger` fib (k `P.subtractInteger` 2)
{-# INLINEABLE fib #-}

fibCompiled :: CompiledCode (Integer -> Integer)
fibCompiled = $$(compile [||fib||])

fibK :: Integer -> Program
fibK k = getPlcNoAnn $ fibCompiled `unsafeApplyCode` liftCodeDef k
