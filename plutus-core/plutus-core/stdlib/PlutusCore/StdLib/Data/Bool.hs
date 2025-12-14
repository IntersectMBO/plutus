{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | @boolean@ and related functions.
module PlutusCore.StdLib.Data.Bool
  ( bool
  , true
  , false
  , ifThenElse
  ) where

import PlutusCore.Core
import PlutusCore.Default.Builtins
import PlutusCore.MkPlc
import PlutusCore.Name.Unique
import PlutusCore.Quote

import PlutusCore.StdLib.Data.Unit

-- | 'Bool' as a PLC type.
bool :: uni `HasTypeLevel` Bool => Type tyname uni ()
bool = mkTyBuiltin @_ @Bool ()

-- | 'True' as a PLC term.
true :: (TermLike term tyname name uni fun, uni `HasTermLevel` Bool) => term ()
true = mkConstant () True

-- | 'False' as a PLC term.
false :: (TermLike term tyname name uni fun, uni `HasTermLevel` Bool) => term ()
false = mkConstant () False

{-| @if_then_else_@ as a PLC term.

> /\(A :: *) -> \(b : Bool) (x y : () -> A) -> IfThenElse {() -> A} b x y () -}
ifThenElse
  :: forall term uni
   . ( TermLike term TyName Name uni DefaultFun
     , uni `HasTypeAndTermLevel` Bool
     , uni `HasTypeAndTermLevel` ()
     )
  => term ()
ifThenElse = runQuote $ do
  a <- freshTyName "a"
  b <- freshName "b"
  x <- freshName "x"
  y <- freshName "y"
  let unitFunA = TyFun () unit (TyVar () a)
  return
    . tyAbs () a (Type ())
    $ mkIterLamAbs
      [ VarDecl () b bool
      , VarDecl () x unitFunA
      , VarDecl () y unitFunA
      ]
    $ mkIterAppNoAnn
      (tyInst () (builtin () IfThenElse) unitFunA)
      [var () b, var () x, var () y, unitval]
