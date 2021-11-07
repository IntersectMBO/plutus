{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}

module PlutusBenchmark.Lists.Sum.Compiled where

import PlutusBenchmark.Common (Term, compiledCodeToTerm)

import PlutusTx qualified as Tx
import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Prelude as Plutus

import Prelude (($!))


---------------- Folding over Scott lists ----------------

{-# INLINABLE foldLeftScott #-}
foldLeftScott :: (b -> a -> b) -> b -> [a] -> b
foldLeftScott _ z []     = z
foldLeftScott f z (x:xs) = foldLeftScott f (f z x) xs

{-# INLINABLE sumLeftScott #-}
sumLeftScott :: [Integer] -> Integer
sumLeftScott l = foldLeftScott (+) 0 l

{-# INLINABLE foldRightScott #-}
foldRightScott :: (a -> b -> b) -> b -> [a] -> b
foldRightScott _ z []     = z
foldRightScott f z (x:xs) = f x $! (foldRightScott f z xs)

{-# INLINABLE sumRightScott #-}
sumRightScott :: [Integer] -> Integer
sumRightScott l = foldRightScott (+) 0 l

-- Compiling to PLC terms

mkSumLeftScottTerm  :: [Integer] -> Term
mkSumLeftScottTerm l = compiledCodeToTerm $ $$(Tx.compile [|| sumLeftScott ||]) `Tx.applyCode` Tx.liftCode l

mkSumRightScottTerm :: [Integer] -> Term
mkSumRightScottTerm l = compiledCodeToTerm $ $$(Tx.compile [|| sumRightScott ||]) `Tx.applyCode` Tx.liftCode l


---------------- Folding over built-in lists ----------------

{-# INLINABLE foldLeftBuiltin #-}
foldLeftBuiltin :: (b -> a -> b) -> b -> BI.BuiltinList a -> b
foldLeftBuiltin f z l = B.matchList l z (\x xs -> (foldLeftBuiltin f (f z x) xs))

{-# INLINABLE sumLeftBuiltin #-}
sumLeftBuiltin :: BI.BuiltinList Integer -> Integer
sumLeftBuiltin l = foldLeftBuiltin B.addInteger 0 l

{-# INLINABLE foldRightBuiltin #-}
foldRightBuiltin :: (a -> b -> b) -> b -> BI.BuiltinList a -> b
foldRightBuiltin f z l = B.matchList l z (\x xs -> f x $! (foldRightBuiltin f z xs))

{-# INLINABLE sumRightBuiltin #-}
sumRightBuiltin :: BI.BuiltinList Integer -> Integer
sumRightBuiltin l = foldRightBuiltin B.addInteger 0 l

-- Compiling to PLC terms

mkSumRightBuiltinTerm :: [Integer] -> Term
mkSumRightBuiltinTerm l = compiledCodeToTerm $ $$(Tx.compile [|| sumRightBuiltin ||]) `Tx.applyCode` Tx.liftCode (BI.BuiltinList l)

mkSumLeftBuiltinTerm :: [Integer] -> Term
mkSumLeftBuiltinTerm l = compiledCodeToTerm $ $$(Tx.compile [|| sumLeftBuiltin ||]) `Tx.applyCode` Tx.liftCode (BI.BuiltinList l)



