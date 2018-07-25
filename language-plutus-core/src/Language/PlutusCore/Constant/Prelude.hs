module Language.PlutusCore.Constant.Prelude
    ( Size
    , builtinTrue
    , builtinFalse
    ) where

import           PlutusPrelude
import           Language.PlutusCore.Type
import           Language.PlutusCore.Name

type Size = Natural

builtinTrue :: Term TyName Name a
builtinTrue = undefined

builtinFalse :: Term TyName Name a
builtinFalse = undefined
