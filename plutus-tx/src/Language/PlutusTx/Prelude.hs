{-# LANGUAGE NoImplicitPrelude #-}
module Language.PlutusTx.Prelude (
    -- $prelude
    -- * String and tracing functions
    toPlutusString,
    trace,
    traceH,
    -- * Error
    error,
    -- * Boolean operators
    and,
    or,
    not,
    -- * Int operators
    gt,
    geq,
    lt,
    leq,
    eq,
    plus,
    minus,
    multiply,
    divide,
    remainder,
    -- * Numbers
    min,
    max,
    -- * Maybe
    isJust,
    isNothing,
    maybe,
    -- * Lists
    null,
    map,
    foldr,
    foldl,
    length,
    all,
    any,
    append,
    filter,
    -- * Hashes
    ByteString,
    sha2_256,
    sha3_256,
    equalsByteString,
    takeByteString,
    dropByteString,
    concatenate,
    verifySignature
    ) where

import           Data.ByteString.Lazy             (ByteString)

import           Language.PlutusTx.Prelude.Stage0
import           Language.PlutusTx.Prelude.Stage1

-- $prelude
-- The PlutusTx Prelude is a collection of useful functions that work with
-- builtin Haskell data types such as 'Maybe' and @[]@ (list).
--
-- Functions from the Prelude can be used with the the typed Template Haskell
-- splice operator @$$()@:
--
-- @
--   import qualified Language.PlutusTx.Prelude as P
--
--   [||  $$(P.traceH) "plutus" ... ||]
-- @
