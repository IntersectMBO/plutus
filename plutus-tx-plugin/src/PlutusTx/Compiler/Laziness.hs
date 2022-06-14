{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}

-- | Simulating laziness.
module PlutusTx.Compiler.Laziness where

import PlutusTx.Compiler.Types
import PlutusTx.PIRTypes

import PlutusIR qualified as PIR

import PlutusCore.Quote

{- Note [Object- vs meta-language combinators]
Many of the things we define as *meta*-langugage combinators (i.e. operations on terms) could be defined
as combinators in the object language (i.e. terms). For example, we can define 'delay' as taking a term
and returning a lambda that takes unit and returns the term, or we could define a 'delay' term

\t : a . \u : unit . t

We generally prefer the metalanguage approach despite the fact that we could share combinators
with the standard library because it makes the generated terms simpler without the need for
a simplifier pass. Also, PLC isn't lazy, so combinators work less well.
-}

delay :: Compiling uni fun m ann => PIRTerm uni fun -> m (PIRTerm uni fun)
delay body = PIR.TyAbs AnnOther <$> liftQuote (freshTyName "dead") <*> pure (PIR.Type AnnOther) <*> pure body

delayType :: Compiling uni fun m ann => PIRType uni -> m (PIRType uni)
delayType orig = PIR.TyForall AnnOther <$> liftQuote (freshTyName "dead") <*> pure (PIR.Type AnnOther) <*> pure orig

delayVar :: Compiling uni fun m ann => PIRVar uni fun -> m (PIRVar uni fun)
delayVar (PIR.VarDecl ann n ty) = do
    ty' <- delayType ty
    pure $ PIR.VarDecl ann n ty'

force
    :: CompilingDefault uni fun m ann
    => PIRTerm uni fun -> m (PIRTerm uni fun)
force thunk = do
    a <- liftQuote (freshTyName "dead")
    let fakeTy = PIR.TyForall AnnOther a (PIR.Type AnnOther) (PIR.TyVar AnnOther a)
    pure $ PIR.TyInst AnnOther thunk fakeTy

maybeDelay :: Compiling uni fun m ann => Bool -> PIRTerm uni fun -> m (PIRTerm uni fun)
maybeDelay yes t = if yes then delay t else pure t

maybeDelayVar :: Compiling uni fun m ann => Bool -> PIRVar uni fun -> m (PIRVar uni fun)
maybeDelayVar yes v = if yes then delayVar v else pure v

maybeDelayType :: Compiling uni fun m ann => Bool -> PIRType uni -> m (PIRType uni)
maybeDelayType yes t = if yes then delayType t else pure t

maybeForce
    :: CompilingDefault uni fun m ann
    => Bool -> PIRTerm uni fun -> m (PIRTerm uni fun)
maybeForce yes t = if yes then force t else pure t
