{-# LANGUAGE OverloadedStrings #-}
-- | Meta-functions relating to functions.
module Language.PlutusCore.StdLib.Meta.Data.Function (constPartial) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote

-- | 'const' as a PLC term.
--
-- > /\(A :: *) -> \(x : A) -> t
constPartial :: TermLike term TyName Name uni fun => term () -> term ()
constPartial t = runQuote $ do
    a <- freshTyName "a"
    x <- freshName "x"
    return
        . tyAbs () a (Type ())
        . lamAbs () x (TyVar () a)
        $ t
