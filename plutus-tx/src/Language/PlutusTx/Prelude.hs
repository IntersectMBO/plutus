-- Need some extra imports from the Prelude for doctests, annoyingly
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fmax-simplifier-iterations=0 #-}

module Language.PlutusTx.Prelude (
    -- $prelude
    -- * Classes
    module Eq,
    module Ord,
    module Semigroup,
    module Monoid,
    module Numeric,
    module Functor,
    module Applicative,
    module Lattice,
    -- * Standard functions
    ($),
    -- * String and tracing functions
    trace,
    traceIfTrue,
    traceIfFalse,
    traceError,
    module String,
    -- * Error
    error,
    check,
    -- * Booleans
    module Bool,
    -- * Int operators
    divide,
    modulo,
    quotient,
    remainder,
    -- * Tuples
    fst,
    snd,
    -- * Maybe
    module Maybe,
    -- * Lists
    module List,
    fold,
    foldMap,
    -- * ByteStrings
    ByteString,
    takeByteString,
    dropByteString,
    concatenate,
    emptyByteString,
    -- * Hashes and Signatures
    sha2_256,
    sha3_256,
    verifySignature,
    -- * Rational numbers
    Rational,
    (%),
    fromInteger,
    round,
    quotRem,
    module Prelude
    ) where

import           Data.String                   (IsString (..))
import           Language.PlutusTx.Applicative as Applicative
import           Language.PlutusTx.Bool        as Bool
import           Language.PlutusTx.Builtins    (ByteString, concatenate, dropByteString, emptyByteString,
                                                equalsByteString, greaterThanByteString, lessThanByteString, sha2_256,
                                                sha3_256, takeByteString, verifySignature)
import qualified Language.PlutusTx.Builtins    as Builtins
import           Language.PlutusTx.Eq          as Eq
import           Language.PlutusTx.Functor     as Functor
import           Language.PlutusTx.Lattice     as Lattice
import           Language.PlutusTx.List        as List
import           Language.PlutusTx.Maybe       as Maybe
import           Language.PlutusTx.Monoid      as Monoid
import           Language.PlutusTx.Numeric     as Numeric
import           Language.PlutusTx.Ord         as Ord
import           Language.PlutusTx.Ratio       as Ratio
import           Language.PlutusTx.Semigroup   as Semigroup
import           Language.PlutusTx.String      as String
import           Prelude                       as Prelude hiding (Applicative (..), Eq (..), Functor (..), Monoid (..),
                                                           Num (..), Ord (..), Rational, Semigroup (..), all, any,
                                                           const, elem, error, filter, foldMap, foldl, foldr, fst, id,
                                                           length, map, max, maybe, min, not, null, quotRem, reverse,
                                                           round, sequence, snd, traverse, zip, (!!), ($), (&&), (++),
                                                           (<$>), (||))

-- this module does lots of weird stuff deliberately
{-# ANN module ("HLint: ignore"::String) #-}

-- $prelude
-- The PlutusTx Prelude is a replacement for the Haskell Prelude that works
-- better with Plutus Tx. You should use it if you're writing code that
-- will be compiled with the Plutus Tx compiler.
-- @
--     {-# LANGUAGE NoImplicitPrelude #-}
--     import Language.PlutusTx.Prelude
-- @

-- $setup
-- >>> :set -XNoImplicitPrelude
-- >>> import Language.PlutusTx.Prelude

{-# INLINABLE error #-}
-- | Terminate the evaluation of the script with an error message.
error :: () -> a
error = Builtins.error

{-# INLINABLE check #-}
-- | Checks a 'Bool' and aborts if it is false.
check :: Bool -> ()
check b = if b then () else error ()

{-# INLINABLE trace #-}
-- | Emit the given string as a trace message before evaluating the argument.
trace :: Builtins.String -> a -> a
-- The builtin trace is just a side-effecting function that returns unit, so
-- we have to be careful to make sure it actually gets evaluated, and not
-- thrown away by GHC or the PIR compiler.
trace str a = case Builtins.trace str of () -> a

{-# INLINABLE traceError #-}
-- | Log a message and then terminate the evaluation with an error.
traceError :: Builtins.String -> a
traceError str = error (trace str ())

{-# INLINABLE traceIfFalse #-}
-- | Emit the given 'String' only if the argument evaluates to 'False'.
traceIfFalse :: Builtins.String -> Bool -> Bool
traceIfFalse str a = if a then True else trace str False

{-# INLINABLE traceIfTrue #-}
-- | Emit the given 'String' only if the argument evaluates to 'True'.
traceIfTrue :: Builtins.String -> Bool -> Bool
traceIfTrue str a = if a then trace str True else False

{-# INLINABLE divide #-}
-- | Integer division, rounding downwards
--
--   >>> divide (-41) 5
--   -9
--
divide :: Integer -> Integer -> Integer
divide = Builtins.divideInteger

{-# INLINABLE modulo #-}
-- | Integer remainder, always positive for a positive divisor
--
--   >>> modulo (-41) 5
--   4
--
modulo :: Integer -> Integer -> Integer
modulo = Builtins.modInteger

{-# INLINABLE quotient #-}
-- | Integer division, rouding towards zero
--
--   >>> quotient (-41) 5
--   -8
--

quotient :: Integer -> Integer -> Integer
quotient = Builtins.quotientInteger

{-# INLINABLE remainder #-}
-- | Integer remainder, same sign as dividend
--
--   >>> remainder (-41) 5
--   -1
--
remainder :: Integer -> Integer -> Integer
remainder = Builtins.remainderInteger

{-# INLINABLE fst #-}
-- | PlutusTx version of 'Data.Tuple.fst'
fst :: (a, b) -> a
fst (a, _) = a

{-# INLINABLE snd #-}
-- | PlutusTx version of 'Data.Tuple.snd'
snd :: (a, b) -> b
snd (_, b) = b

{-# INLINABLE fold #-}
fold :: Monoid m => [m] -> m
fold = foldr (<>) mempty

{-# INLINABLE foldMap #-}
foldMap :: Monoid m => (a -> m) -> [a] -> m
foldMap f = foldr (\a m -> f a <> m) mempty

infixr 0 $
-- Normal $ is levity-polymorphic, which we can't handle.
{-# INLINABLE ($) #-}
-- | Plutus Tx version of 'Data.Function.($)'.
($) :: (a -> b) -> a -> b
f $ a = f a
