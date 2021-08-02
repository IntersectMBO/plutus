{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Trace (
  trace,
  traceError,
  traceIfFalse,
  traceIfTrue
  ) where

import           PlutusTx.Builtins as Builtins
import           Prelude           hiding (error)

{-# INLINABLE traceError #-}
-- | Log a message and then terminate the evaluation with an error.
traceError :: Builtins.BuiltinString -> a
traceError str = error (trace str ())

{-# INLINABLE traceIfFalse #-}
-- | Emit the given 'BuiltinString' only if the argument evaluates to 'False'.
traceIfFalse :: Builtins.BuiltinString -> Bool -> Bool
traceIfFalse str a = if a then True else trace str False

{-# INLINABLE traceIfTrue #-}
-- | Emit the given 'BuiltinString' only if the argument evaluates to 'True'.
traceIfTrue :: Builtins.BuiltinString -> Bool -> Bool
traceIfTrue str a = if a then trace str True else False
