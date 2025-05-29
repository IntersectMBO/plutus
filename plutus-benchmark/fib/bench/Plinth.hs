{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O2 #-}

module Plinth (fib, fib25, fib29, fib31, fib33, fib15, fib20) where

-- import PlutusTx.Prelude qualified as P
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
{-# INLINABLE fib #-}

fibCompiled :: CompiledCode (Integer -> Integer)
fibCompiled = $$( compile [|| fib ||])

fibK :: Integer -> Program
fibK k = getPlcNoAnn $ fibCompiled `unsafeApplyCode` liftCodeDef k

fib25 :: Program
fib25 = fibK 25

fib29 :: Program
fib29 = fibK 29

fib31 :: Program
fib31 = fibK 31

fib33 :: Program
fib33 = fibK 33

fib15 :: Program
fib15 = fibK 15

fib20 :: Program
fib20 = fibK 20
