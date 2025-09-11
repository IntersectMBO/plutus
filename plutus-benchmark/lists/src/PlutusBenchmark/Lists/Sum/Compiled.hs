-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}

module PlutusBenchmark.Lists.Sum.Compiled where

import PlutusBenchmark.Common (Term, compiledCodeToTerm)

import PlutusTx qualified as Tx
import PlutusTx.Builtins qualified as B
import PlutusTx.Builtins.Internal qualified as BI
import PlutusTx.Plugin ()
import PlutusTx.Prelude

import Prelude (($!))


---------------- Folding over Scott lists ----------------

foldLeftScott :: (b -> a -> b) -> b -> [a] -> b
foldLeftScott _ z []     = z
foldLeftScott f z (x:xs) = foldLeftScott f (f z x) xs
{-# INLINABLE foldLeftScott #-}

sumLeftScott :: [Integer] -> Integer
sumLeftScott l = foldLeftScott (+) 0 l
{-# INLINABLE sumLeftScott #-}

foldRightScott :: (a -> b -> b) -> b -> [a] -> b
foldRightScott _ z []     = z
foldRightScott f z (x:xs) = f x $! (foldRightScott f z xs)
{-# INLINABLE foldRightScott #-}

sumRightScott :: [Integer] -> Integer
sumRightScott l = foldRightScott (+) 0 l
{-# INLINABLE sumRightScott #-}

-- Compiling to PLC terms

mkSumLeftScottCode :: [Integer] -> Tx.CompiledCode Integer
mkSumLeftScottCode l = $$(Tx.compile [|| sumLeftScott ||]) `Tx.unsafeApplyCode` Tx.liftCodeDef l

mkSumLeftScottTerm  :: [Integer] -> Term
mkSumLeftScottTerm l = compiledCodeToTerm $ mkSumLeftScottCode l

mkSumRightScottCode :: [Integer] -> Tx.CompiledCode Integer
mkSumRightScottCode l = $$(Tx.compile [|| sumRightScott ||]) `Tx.unsafeApplyCode` Tx.liftCodeDef l

mkSumRightScottTerm :: [Integer] -> Term
mkSumRightScottTerm l = compiledCodeToTerm $ mkSumRightScottCode l

---------------- Folding over built-in lists ----------------

foldLeftBuiltin :: (b -> a -> b) -> b -> BuiltinList a -> b
foldLeftBuiltin f z l = B.matchList' l z (\x xs -> (foldLeftBuiltin f (f z x) xs))
{-# INLINABLE foldLeftBuiltin #-}

sumLeftBuiltin :: BuiltinList Integer -> Integer
sumLeftBuiltin l = foldLeftBuiltin B.addInteger 0 l
{-# INLINABLE sumLeftBuiltin #-}

foldRightBuiltin :: (a -> b -> b) -> b -> BuiltinList a -> b
foldRightBuiltin f z l = B.matchList' l z (\x xs -> f x $! (foldRightBuiltin f z xs))
{-# INLINABLE foldRightBuiltin #-}

sumRightBuiltin :: BuiltinList Integer -> Integer
sumRightBuiltin l = foldRightBuiltin B.addInteger 0 l
{-# INLINABLE sumRightBuiltin #-}

-- Compiling to PLC terms

mkSumRightBuiltinCode :: [Integer] -> Tx.CompiledCode Integer
mkSumRightBuiltinCode l = $$(Tx.compile [|| sumRightBuiltin ||]) `Tx.unsafeApplyCode` Tx.liftCodeDef (BI.BuiltinList l)

mkSumRightBuiltinTerm :: [Integer] -> Term
mkSumRightBuiltinTerm l = compiledCodeToTerm $ mkSumRightBuiltinCode l

mkSumLeftBuiltinCode :: [Integer] -> Tx.CompiledCode Integer
mkSumLeftBuiltinCode l = $$(Tx.compile [|| sumLeftBuiltin ||]) `Tx.unsafeApplyCode` Tx.liftCodeDef (BI.BuiltinList l)

mkSumLeftBuiltinTerm :: [Integer] -> Term
mkSumLeftBuiltinTerm l = compiledCodeToTerm $ mkSumLeftBuiltinCode l

---------------- Folding over "data lists" ----------------

{- Note [Data lists]
"Data lists" are lists implemented just using Data as the structural component.
That is, rather than relying on the PIR compiler or explicit Scott encoding, we
use the Constr constructor of Data.

This is a slightly odd way to do things, but is apparently how Aiken encodes
*all* structured data, so it's instructive to benchmark it against other approaches.

Data lists don't perform that well, unsurprisingly, since constructing/deconstructing
a list encoded in this way requires several builtin operations to get through the
`Constr`, the tuple of its arguments, and the list of constructor args.
-}

type DataList = BuiltinData

matchDataList :: forall  r . DataList -> r -> (BuiltinData -> DataList -> r) -> r
matchDataList l nilCase consCase =
  B.matchData'
    l
    handleConstr
    (\_ -> error ())
    (\_ -> error ())
    (\_ -> error ())
    (\_ -> error ())
  where
    handleConstr tag values =
      if tag == 0 then nilCase
      else if tag == 1 then B.matchList values error (\h t -> consCase h (BI.head t))
      else error ()

foldLeftData :: (b -> BuiltinData -> b) -> b -> DataList -> b
foldLeftData f z l = matchDataList l z (\x xs -> (foldLeftData f (f z x) xs))
{-# INLINABLE foldLeftData #-}

sumLeftData :: DataList -> Integer
sumLeftData l = foldLeftData (\acc d -> B.addInteger acc (BI.unsafeDataAsI d)) 0 l
{-# INLINABLE sumLeftData #-}

foldRightData :: (BuiltinData -> b -> b) -> b -> DataList -> b
foldRightData f z l = matchDataList l z (\x xs -> f x $! (foldRightData f z xs))
{-# INLINABLE foldRightData #-}

sumRightData :: DataList -> Integer
sumRightData l = foldRightData (\d acc -> B.addInteger (BI.unsafeDataAsI d) acc) 0 l
{-# INLINABLE sumRightData #-}

-- Compiling to PLC terms

listToDataList :: [Integer] -> DataList
listToDataList l = Tx.dataToBuiltinData (go l)
  where
    go []     = Tx.Constr 0 []
    go (x:xs) = Tx.Constr 1 [Tx.I x, go xs]

mkSumRightDataCode :: [Integer] -> Tx.CompiledCode Integer
mkSumRightDataCode l = $$(Tx.compile [|| sumRightData ||]) `Tx.unsafeApplyCode` Tx.liftCodeDef (listToDataList l)

mkSumRightDataTerm :: [Integer] -> Term
mkSumRightDataTerm l = compiledCodeToTerm $ mkSumRightDataCode l

mkSumLeftDataCode :: [Integer] -> Tx.CompiledCode Integer
mkSumLeftDataCode l = $$(Tx.compile [|| sumLeftData ||]) `Tx.unsafeApplyCode` Tx.liftCodeDef (listToDataList l)

mkSumLeftDataTerm :: [Integer] -> Term
mkSumLeftDataTerm l = compiledCodeToTerm $ mkSumLeftDataCode l
