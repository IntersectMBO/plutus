{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
-- | Simulating laziness.
module PlutusTx.Compiler.Laziness where

import {-# SOURCE #-}           PlutusTx.Compiler.Expr
import                          PlutusTx.Compiler.Type
import                          PlutusTx.Compiler.Types
import                          PlutusTx.PIRTypes

import                qualified PlutusIR                as PIR

import                          PlutusCore.Quote

import                qualified GhcPlugins              as GHC

{- Note [Object- vs meta-language combinators]
Many of the things we define as *meta*-langugage combinators (i.e. operations on terms) could be defined
as combinators in the object language (i.e. terms). For example, we can define 'delay' as taking a term
and returning a lambda that takes unit and returns the term, or we could define a 'delay' term

\t : a . \u : unit . t

We generally prefer the metalanguage approach despite the fact that we could share combinators
with the standard library because it makes the generated terms simpler without the need for
a simplifier pass. Also, PLC isn't lazy, so combinators work less well.
-}

delay :: Compiling uni fun m => PIRTerm uni fun -> m (PIRTerm uni fun)
delay body = PIR.LamAbs () <$> liftQuote (freshName "thunk") <*> compileType GHC.unitTy <*> pure body

delayType :: Compiling uni fun m => PIRType uni -> m (PIRType uni)
delayType orig = PIR.TyFun () <$> compileType GHC.unitTy <*> pure orig

delayVar :: Compiling uni fun m => PIRVar uni fun -> m (PIRVar uni fun)
delayVar (PIR.VarDecl () n ty) = do
    ty' <- delayType ty
    pure $ PIR.VarDecl () n ty'

force
    :: CompilingDefault uni fun m
    => PIRTerm uni fun -> m (PIRTerm uni fun)
force thunk = PIR.Apply () thunk <$> compileExpr (GHC.Var GHC.unitDataConId)

maybeDelay :: Compiling uni fun m => Bool -> PIRTerm uni fun -> m (PIRTerm uni fun)
maybeDelay yes t = if yes then delay t else pure t

maybeDelayVar :: Compiling uni fun m => Bool -> PIRVar uni fun -> m (PIRVar uni fun)
maybeDelayVar yes v = if yes then delayVar v else pure v

maybeDelayType :: Compiling uni fun m => Bool -> PIRType uni -> m (PIRType uni)
maybeDelayType yes t = if yes then delayType t else pure t

maybeForce
    :: CompilingDefault uni fun m
    => Bool -> PIRTerm uni fun -> m (PIRTerm uni fun)
maybeForce yes t = if yes then force t else pure t
