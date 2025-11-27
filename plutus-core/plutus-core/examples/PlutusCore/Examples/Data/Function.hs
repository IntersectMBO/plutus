{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Examples.Data.Function
  ( unsafeCoerce
  ) where

import PlutusCore.Core
import PlutusCore.MkPlc
import PlutusCore.Name.Unique
import PlutusCore.Quote

import PlutusCore.StdLib.Data.Function

unsafeCoerce :: Term TyName Name uni fun ()
unsafeCoerce = runQuote $ do
  a <- freshTyName "a"
  b <- freshTyName "b"
  return
    . TyAbs () a (Type ())
    . TyAbs () b (Type ())
    . Apply () (mkIterInstNoAnn fix [TyVar () a, TyVar () b])
    . TyInst () idFun
    $ TyFun () (TyVar () a) (TyVar () b)
