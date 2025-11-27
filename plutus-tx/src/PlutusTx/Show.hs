{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module PlutusTx.Show
  ( Show (..)
  , ShowS
  , toDigits
  , showString
  , showSpace
  , showCommaSpace
  , showParen
  , appPrec
  , appPrec1
  , deriveShow
  ) where

import PlutusTx.Base
import PlutusTx.Bool
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Either
import PlutusTx.List (foldr)
import PlutusTx.Maybe
import PlutusTx.Prelude
import PlutusTx.Show.TH

instance Show Builtins.Integer where
  {-# INLINEABLE showsPrec #-}
  showsPrec p n =
    if n < 0
      then showString "-" . showsPrec p (negate n)
      else foldr alg id (toDigits n)
    where
      alg :: Builtins.Integer -> ShowS -> ShowS
      alg digit acc =
        showString
          ( if
              | digit == 0 -> "0"
              | digit == 1 -> "1"
              | digit == 2 -> "2"
              | digit == 3 -> "3"
              | digit == 4 -> "4"
              | digit == 5 -> "5"
              | digit == 6 -> "6"
              | digit == 7 -> "7"
              | digit == 8 -> "8"
              | digit == 9 -> "9"
              | otherwise -> "<invalid digit>"
          )
          . acc

-- | Convert a non-negative integer to individual digits.
toDigits :: Builtins.Integer -> [Builtins.Integer]
toDigits = go []
  where
    go acc n = case n `quotRem` 10 of
      (q, r) ->
        if q == 0
          then r : acc
          else go (r : acc) q
{-# INLINEABLE toDigits #-}

instance Show Builtins.BuiltinByteString where
  {-# INLINEABLE showsPrec #-}
  -- Base16-encode the ByteString and show the result.
  showsPrec _ s = foldr alg id (enumFromTo 0 (len - 1))
    where
      len = Builtins.lengthOfByteString s

      showWord8 :: Builtins.Integer -> ShowS
      showWord8 x =
        toHex (x `Builtins.divideInteger` 16)
          . toHex (x `Builtins.modInteger` 16)

      toHex :: Integer -> ShowS
      toHex x =
        if
          | x <= 9 -> showsPrec 0 x
          | x == 10 -> showString "a"
          | x == 11 -> showString "b"
          | x == 12 -> showString "c"
          | x == 13 -> showString "d"
          | x == 14 -> showString "e"
          | x == 15 -> showString "f"
          | otherwise -> showString "<invalid byte>"
      alg :: Builtins.Integer -> ShowS -> ShowS
      alg i acc = showWord8 (Builtins.indexByteString s i) . acc

instance Show Builtins.BuiltinString where
  {-# INLINEABLE showsPrec #-}
  -- Add quotes to the given string. `Prelude.show @String` uses @showLitChar@ to process
  -- non-ascii characters and escape characters, in additional to adding quotes. We have
  -- no builtin that operates on `Char`, so we cannot implement the same behavior.
  showsPrec _ s = showString "\"" . showString s . showString "\""

instance Show Builtins.BuiltinData where
  {-# INLINEABLE showsPrec #-}
  showsPrec p d = showsPrec p (Builtins.serialiseData d)

instance Show Bool where
  {-# INLINEABLE show #-}
  show b = if b then "True" else "False"

instance Show () where
  {-# INLINEABLE show #-}
  show () = "()"

-- It is possible to make it so that when `a` is a builtin type, `show (xs :: [a])`
-- is compiled into a single `showConstant` call, rathern than `length xs` calls.
-- To do so the plugin would need to try to solve the @uni `HasTermLevel` [a]@ constraint,
-- and branch based on whether it is solvable. But the complexity doesn't seem to
-- be worth it: the saving in budget is likely small, and on mainnet the trace messages
-- are often erased anyway.
--
-- Same for the `Show (a, b)` instance.
instance Show a => Show [a] where
  {-# INLINEABLE showsPrec #-}
  showsPrec _ = showList (showsPrec 0)

showList :: forall a. (a -> ShowS) -> [a] -> ShowS
showList showElem = \case
  [] -> showString "[]"
  x : xs ->
    showString "["
      . showElem x
      . foldr alg id xs
      . showString "]"
    where
      alg :: a -> ShowS -> ShowS
      alg a acc = showString "," . showElem a . acc
{-# INLINEABLE showList #-}

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
