{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Simulating laziness.
module Language.PlutusTx.Compiler.Laziness where

import {-# SOURCE #-} Language.PlutusTx.Compiler.Expr
import {-# SOURCE #-} Language.PlutusTx.Compiler.Type
import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.PIRTypes

import qualified Language.PlutusIR                as PIR

import           Language.PlutusCore.Quote

import qualified GhcPlugins                       as GHC

{- Note [Object- vs meta-language combinators]
Many of the things we define as *meta*-langugage combinators (i.e. operations on terms) could be defined
as combinators in the object language (i.e. terms). For example, we can define 'delay' as taking a term
and returning a lambda that takes unit and returns the term, or we could define a 'delay' term

\t : a . \u : unit . t

We generally prefer the metalanguage approach despite the fact that we could share combinators
with the standard library because it makes the generated terms simpler without the need for
a simplifier pass. Also, PLC isn't lazy, so combinators work less well.
-}

delay :: Compiling m => PIRTerm -> m PIRTerm
delay body = PIR.LamAbs () <$> liftQuote (freshName () "thunk") <*> compileType GHC.unitTy <*> pure body

delayType :: Compiling m => PIRType -> m PIRType
delayType orig = PIR.TyFun () <$> compileType GHC.unitTy <*> pure orig

delayVar :: Compiling m => PIRVar -> m PIRVar
delayVar (PIR.VarDecl () n ty) = do
    ty' <- delayType ty
    pure $ PIR.VarDecl () n ty'

force :: Compiling m => PIRTerm -> m PIRTerm
force thunk = PIR.Apply () thunk <$> compileExpr (GHC.Var GHC.unitDataConId)

maybeDelay :: Compiling m => Bool -> PIRTerm -> m PIRTerm
maybeDelay yes t = if yes then delay t else pure t

maybeDelayVar :: Compiling m => Bool -> PIRVar -> m PIRVar
maybeDelayVar yes v = if yes then delayVar v else pure v

maybeDelayType :: Compiling m => Bool -> PIRType -> m PIRType
maybeDelayType yes t = if yes then delayType t else pure t

maybeForce :: Compiling m => Bool -> PIRTerm -> m PIRTerm
maybeForce yes t = if yes then force t else pure t
