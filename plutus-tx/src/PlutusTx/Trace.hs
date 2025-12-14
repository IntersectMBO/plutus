{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

module PlutusTx.Trace
  ( trace
  , traceError
  , traceIfFalse
  , traceIfTrue
  , traceBool
  ) where

import PlutusTx.Bool
import PlutusTx.Builtins as Builtins

-- | Log a message and then terminate the evaluation with an error.
traceError :: Builtins.BuiltinString -> a
traceError str = error (trace str ())
{-# INLINEABLE traceError #-}

-- | Emit the given 'BuiltinString' only if the argument evaluates to 'False'.
traceIfFalse :: Builtins.BuiltinString -> Bool -> Bool
traceIfFalse str a = if a then True else trace str False
{-# INLINEABLE traceIfFalse #-}

-- | Emit the given 'BuiltinString' only if the argument evaluates to 'True'.
traceIfTrue :: Builtins.BuiltinString -> Bool -> Bool
traceIfTrue str a = if a then trace str True else False
{-# INLINEABLE traceIfTrue #-}

{-| Emit one of two 'BuiltinString' depending on whether or not the argument
evaluates to 'True' or 'False'. -}
traceBool :: BuiltinString -> BuiltinString -> Bool -> Bool
traceBool trueLabel falseLabel c = if c then trace trueLabel True else trace falseLabel False
{-# INLINEABLE traceBool #-}
