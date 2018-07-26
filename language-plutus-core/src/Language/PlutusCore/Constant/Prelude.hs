module Language.PlutusCore.Constant.Prelude
    ( Size
    , builtinTrue
    , builtinFalse
    ) where

import           PlutusPrelude
import           Language.PlutusCore.Type
import           Language.PlutusCore.Name

type Size = Natural

-- | Church-encoded @True@ as a PLC term.
--
-- > /\a -> \(x y : () -> a) -> x ()
builtinTrue :: Term TyName Name a
builtinTrue = undefined

-- | Church-encoded @False@ as a PLC term.
--
-- > /\a -> \(x y : () -> a) -> y ()
builtinFalse :: Term TyName Name a
builtinFalse = undefined
