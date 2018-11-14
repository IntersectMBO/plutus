{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Simulating laziness.
module Language.Plutus.CoreToPLC.Compiler.Laziness where

import {-# SOURCE #-} Language.Plutus.CoreToPLC.Compiler.Expr
import {-# SOURCE #-} Language.Plutus.CoreToPLC.Compiler.Type
import           Language.Plutus.CoreToPLC.Compiler.Types
import           Language.Plutus.CoreToPLC.PIRTypes

import qualified Language.PlutusIR                        as PIR

import           Language.PlutusCore.Quote

import qualified GhcPlugins                               as GHC

{- Note [Object- vs meta-language combinators]
Many of the things we define as *meta*-langugage combinators (i.e. operations on terms) could be defined
as combinators in the object language (i.e. terms). For example, we can define 'delay' as taking a term
and returning a lambda that takes unit and returns the term, or we could define a 'delay' term

\t : a . \u : unit . t

We generally prefer the metalanguage approach despite the fact that we could share combinators
with the standard library because it makes the generated terms simpler without the need for
a simplifier pass. Also, PLC isn't lazy, so combinators work less well.
-}

delay :: Converting m => PIRTerm -> m PIRTerm
delay body = PIR.LamAbs () <$> liftQuote (freshName () "thunk") <*> convType GHC.unitTy <*> pure body

delayType :: Converting m => PIRType -> m PIRType
delayType orig = PIR.TyFun () <$> convType GHC.unitTy <*> pure orig

force :: Converting m => PIRTerm -> m PIRTerm
force thunk = PIR.Apply () thunk <$> convExpr (GHC.Var GHC.unitDataConId)

maybeDelay :: Converting m => Bool -> PIRTerm -> m PIRTerm
maybeDelay yes t = if yes then delay t else pure t

maybeDelayType :: Converting m => Bool -> PIRType -> m PIRType
maybeDelayType yes t = if yes then delayType t else pure t

maybeForce :: Converting m => Bool -> PIRTerm -> m PIRTerm
maybeForce yes t = if yes then force t else pure t
