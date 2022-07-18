{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Show.TH where

import PlutusTx.Builtins
import PlutusTx.Foldable
import PlutusTx.List

class Show a where
    {-# MINIMAL showsPrec | show #-}

    {-# INLINEABLE showsPrec #-}
    showsPrec :: Integer -> a -> ShowS
    showsPrec _ x ss = show x : ss

    {-# INLINEABLE show #-}
    show :: a -> BuiltinString
    show x = concatBuiltinStrings (showsPrec 0 x [])

{- | Currently the only way to concatenate `BuiltinString`s is `appendString`, whose cost
 is linear in the total length of the two strings. A naive concatenation of multiple
 `BuiltinString`s costs @O(n^2)@ in the worst case, where @n@ is the total length. By
 collecting the `BuiltinString`s in a list and concatenating them in the end, the cost
 can be reduced to @O(n*logn)@. If we add a @concatStrings@ builtin function in the future,
 the cost can be further reduced to @O(n)@.

 Like `GHC.Show.ShowS`, the purpose of the function type here is to turn list concatenation
 into function composition.
-}
type ShowS = [BuiltinString] -> [BuiltinString]

{-# INLINEABLE showString #-}
showString :: BuiltinString -> ShowS
showString = (:)

{-# INLINEABLE concatBuiltinStrings #-}
concatBuiltinStrings :: [BuiltinString] -> BuiltinString
concatBuiltinStrings = \case
    [] -> ""
    [x] -> x
    xs ->
        let (ys, zs) = splitAt (length xs `divideInteger` 2) xs
         in concatBuiltinStrings ys `appendString` concatBuiltinStrings zs

-----------------------------------------------------------
-- TODO: TH machinery for deriving `Show` here
