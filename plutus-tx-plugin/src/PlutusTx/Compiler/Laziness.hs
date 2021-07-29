{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}
-- | Simulating laziness.
module PlutusTx.Compiler.Laziness where

import           PlutusTx.PIRTypes

import qualified PlutusIR          as PIR

{- Note [Object- vs meta-language combinators]
Many of the things we define as *meta*-langugage combinators (i.e. operations on terms) could be defined
as combinators in the object language (i.e. terms). For example, we can define 'delay' as taking a term
and returning a lambda that takes unit and returns the term, or we could define a 'delay' term

\t : a . \u : unit . t

We generally prefer the metalanguage approach despite the fact that we could share combinators
with the standard library because it makes the generated terms simpler without the need for
a simplifier pass. Also, PLC isn't lazy, so combinators work less well.
-}

delay :: PIRTerm uni fun -> PIRTerm uni fun
delay = PIR.Delay ()

delayType :: PIRType uni -> PIRType uni
delayType = PIR.TyDelayed ()

delayVar :: PIRVar uni fun -> PIRVar uni fun
delayVar (PIR.VarDecl () n ty) = PIR.VarDecl () n $ delayType ty

force :: PIRTerm uni fun -> PIRTerm uni fun
force = PIR.Force ()

maybeDelay :: Bool -> PIRTerm uni fun -> PIRTerm uni fun
maybeDelay yes t = if yes then delay t else t

maybeDelayVar :: Bool -> PIRVar uni fun -> PIRVar uni fun
maybeDelayVar yes v = if yes then delayVar v else v

maybeDelayType :: Bool -> PIRType uni -> PIRType uni
maybeDelayType yes t = if yes then delayType t else t

maybeForce :: Bool -> PIRTerm uni fun -> PIRTerm uni fun
maybeForce yes t = if yes then force t else t
