{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusTx.Show (
    Show (..),
) where

import PlutusTx.Base
import PlutusTx.Bool
import PlutusTx.Builtins
import PlutusTx.Builtins.Internal qualified
import PlutusTx.Foldable (foldl)
import PlutusTx.Show.TH (Show (..), ShowS, showString)

instance Show Integer where
    {-# INLINEABLE show #-}
    show = displayConstant

instance Show BuiltinByteString where
    {-# INLINEABLE show #-}
    show x = displayConstant (fromBuiltin x)

instance Show BuiltinData where
    {-# INLINEABLE show #-}
    show (PlutusTx.Builtins.Internal.BuiltinData x) = displayConstant x

instance Show BuiltinString where
    {-# INLINEABLE show #-}
    show x = displayConstant (fromBuiltin x)

instance Show Bool where
    {-# INLINEABLE show #-}
    show x = displayConstant x

instance Show () where
    {-# INLINEABLE show #-}
    show () = displayConstant ()

-- It is possible to make it so that when `a` is a builtin type, `show (xs :: [a])`
-- is compiled into a single `displayConstant` call, rathern than `length xs` calls.
-- To do so the plugin would need to try to solve the `PrettyConst [a]` constraint,
-- and branch based on whether it is solvable. But the complexity doesn't seem to
-- be worth it: the saving in budget is likely small, and on mainnet the trace messages
-- are often erased anyway.
--
-- Same for the `Show (a, b)` instance.
instance Show a => Show [a] where
    showsPrec _ = \case
        [] -> showString "[]"
        x : xs ->
            showString "["
                . showsPrec 0 x
                . foldl alg id xs
                . showString "]"
          where
            alg :: ShowS -> a -> ShowS
            alg acc a = acc . showString "," . showsPrec 0 a

-----------------------------------------------------------
-- TODO: derive instances for tuples, Maybe, Either and other common types here.
