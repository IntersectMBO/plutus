{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusTx.Show (
    Show (..),
    ShowS,
    showString,
    showSpace,
    showCommaSpace,
    showParen,
    appPrec,
    appPrec1,
    deriveShow,
) where

import PlutusTx.Base
import PlutusTx.Bool
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Either
import PlutusTx.Foldable (foldl)
import PlutusTx.Maybe
import PlutusTx.Show.TH

instance Show Builtins.Integer where
    {-# INLINEABLE show #-}
    show = Builtins.showInteger

instance Show Builtins.BuiltinByteString where
    {-# INLINEABLE show #-}
    show = Builtins.showByteString

instance Show Builtins.BuiltinData where
    {-# INLINEABLE show #-}
    show = Builtins.showData

instance Show Builtins.BuiltinString where
    {-# INLINEABLE show #-}
    show = Builtins.showString

instance Show Bool where
    {-# INLINEABLE show #-}
    show = Builtins.showBool

instance Show () where
    {-# INLINEABLE show #-}
    show () = "()"

-- It is possible to make it so that when `a` is a builtin type, `show (xs :: [a])`
-- is compiled into a single `showConstant` call, rathern than `length xs` calls.
-- To do so the plugin would need to try to solve the @uni `Contains` [a]@ constraint,
-- and branch based on whether it is solvable. But the complexity doesn't seem to
-- be worth it: the saving in budget is likely small, and on mainnet the trace messages
-- are often erased anyway.
--
-- Same for the `Show (a, b)` instance.
instance Show a => Show [a] where
    {-# INLINEABLE showsPrec #-}
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

deriveShow ''(,)
deriveShow ''(,,)
deriveShow ''(,,,)
deriveShow ''(,,,,)
deriveShow ''(,,,,,)
deriveShow ''(,,,,,,)
deriveShow ''(,,,,,,,)
deriveShow ''(,,,,,,,,)
deriveShow ''(,,,,,,,,,)
deriveShow ''(,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,,,,,,,)
deriveShow ''(,,,,,,,,,,,,,,,,,,,,,,,,,,)
deriveShow ''Maybe
deriveShow ''Either
