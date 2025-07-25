{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}

module PlutusBenchmark.NoFib.Fibonacci where

import PlutusBenchmark.Common (Term, compiledCodeToTerm)

import PlutusTx qualified as Tx
import PlutusTx.Plugin ()
import PlutusTx.Prelude as Tx

fib :: Integer -> Integer
fib k
  | k == 0 = 0
  | k == 1 = 1
  | otherwise = fib (k-1) + fib (k-2)
{-# INLINABLE fib #-}

runFibonacci :: Integer -> Integer
runFibonacci n = fib n
{-# INLINABLE runFibonacci #-}

mkFibCode :: Integer -> Tx.CompiledCode Integer
mkFibCode n =
       $$(Tx.compile [|| runFibonacci ||])
             `Tx.unsafeApplyCode` Tx.liftCodeDef n

mkFibTerm :: Integer -> Term
mkFibTerm n = compiledCodeToTerm $ mkFibCode n

