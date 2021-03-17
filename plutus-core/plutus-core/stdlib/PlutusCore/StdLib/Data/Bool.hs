-- | @boolean@ and related functions.

{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusCore.StdLib.Data.Bool
    ( bool
    , true
    , false
    , ifThenElse
    ) where

import           PlutusCore.Builtins
import           PlutusCore.Core
import           PlutusCore.MkPlc
import           PlutusCore.Name
import           PlutusCore.Quote
import           PlutusCore.Universe

import           PlutusCore.StdLib.Data.Unit

-- | 'Bool' as a PLC type.
bool :: uni `Includes` Bool => Type TyName uni ()
bool = mkTyBuiltin @Bool ()

-- | 'True' as a PLC term.
true :: (TermLike term TyName Name uni fun, uni `Includes` Bool) => term ()
true = mkConstant () True

-- | 'False' as a PLC term.
false :: (TermLike term TyName Name uni fun, uni `Includes` Bool) => term ()
false = mkConstant () False

-- | @if_then_else_@ as a PLC term.
--
-- > /\(A :: *) -> \(b : Bool) (x y : () -> A) -> IfThenElse {() -> A} b x y ()
ifThenElse :: (TermLike term TyName Name uni DefaultFun, uni `IncludesAll` '[Bool, ()]) => term ()
ifThenElse = runQuote $ do
    a <- freshTyName "a"
    b <- freshName "b"
    x <- freshName "x"
    y <- freshName "y"
    let unitFunA = TyFun () unit (TyVar () a)
    return
       . tyAbs () a (Type ())
      $ mkIterLamAbs [
          VarDecl () b bool,
          VarDecl () x unitFunA,
          VarDecl () y unitFunA
          ]
      $ mkIterApp ()
          (tyInst () (builtin () IfThenElse) unitFunA)
          [var () b, var () x, var () y, unitval]
