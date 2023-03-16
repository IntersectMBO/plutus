-- editorconfig-checker-disable-file
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

mkSumLeftScottCode :: [Integer] -> Tx.CompiledCode Integer
mkSumLeftScottCode l = $$(Tx.compile [|| sumLeftScott ||]) `Tx.unsafeApplyCode` Tx.liftCode l

mkSumLeftScottTerm  :: [Integer] -> Term
mkSumLeftScottTerm l = compiledCodeToTerm $ mkSumLeftScottCode l

mkSumRightScottCode :: [Integer] -> Tx.CompiledCode Integer
mkSumRightScottCode l = $$(Tx.compile [|| sumRightScott ||]) `Tx.unsafeApplyCode` Tx.liftCode l

mkSumRightScottTerm :: [Integer] -> Term
mkSumRightScottTerm l = compiledCodeToTerm $ mkSumRightScottCode l

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

mkSumRightBuiltinCode :: [Integer] -> Tx.CompiledCode Integer
mkSumRightBuiltinCode l = $$(Tx.compile [|| sumRightBuiltin ||]) `Tx.unsafeApplyCode` Tx.liftCode (BI.BuiltinList l)

mkSumRightBuiltinTerm :: [Integer] -> Term
mkSumRightBuiltinTerm l = compiledCodeToTerm $ mkSumRightBuiltinCode l

mkSumLeftBuiltinCode :: [Integer] -> Tx.CompiledCode Integer
mkSumLeftBuiltinCode l = $$(Tx.compile [|| sumLeftBuiltin ||]) `Tx.unsafeApplyCode` Tx.liftCode (BI.BuiltinList l)

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
      else if tag == 1 then consCase (BI.head values) (BI.head (BI.tail values))
      else error ()

{-# INLINABLE foldLeftData #-}
foldLeftData :: (b -> BuiltinData -> b) -> b -> DataList -> b
foldLeftData f z l = matchDataList l z (\x xs -> (foldLeftData f (f z x) xs))

{-# INLINABLE sumLeftData #-}
sumLeftData :: DataList -> Integer
sumLeftData l = foldLeftData (\acc d -> B.addInteger acc (BI.unsafeDataAsI d)) 0 l

{-# INLINABLE foldRightData #-}
foldRightData :: (BuiltinData -> b -> b) -> b -> DataList -> b
foldRightData f z l = matchDataList l z (\x xs -> f x $! (foldRightData f z xs))

{-# INLINABLE sumRightData #-}
sumRightData :: DataList -> Integer
sumRightData l = foldRightData (\d acc -> B.addInteger (BI.unsafeDataAsI d) acc) 0 l

-- Compiling to PLC terms

listToDataList :: [Integer] -> DataList
listToDataList l = Tx.dataToBuiltinData (go l)
  where
    go []     = Tx.Constr 0 []
    go (x:xs) = Tx.Constr 1 [Tx.I x, go xs]

mkSumRightDataCode :: [Integer] -> Tx.CompiledCode Integer
mkSumRightDataCode l = $$(Tx.compile [|| sumRightData ||]) `Tx.unsafeApplyCode` Tx.liftCode (listToDataList l)

mkSumRightDataTerm :: [Integer] -> Term
mkSumRightDataTerm l = compiledCodeToTerm $ mkSumRightDataCode l

mkSumLeftDataCode :: [Integer] -> Tx.CompiledCode Integer
mkSumLeftDataCode l = $$(Tx.compile [|| sumLeftData ||]) `Tx.unsafeApplyCode` Tx.liftCode (listToDataList l)

mkSumLeftDataTerm :: [Integer] -> Term
mkSumLeftDataTerm l = compiledCodeToTerm $ mkSumLeftDataCode l
