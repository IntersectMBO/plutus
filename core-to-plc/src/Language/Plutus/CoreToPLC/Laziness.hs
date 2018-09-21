{-# LANGUAGE OverloadedStrings #-}
-- | Simulating laziness.
module Language.Plutus.CoreToPLC.Laziness where

import qualified Language.PlutusCore                  as PLC
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Data.Unit as Unit

{- Note [Object- vs meta-language combinators]
Many of the things we define as *meta*-langugage combinators (i.e. operations on terms) could be defined
as combinators in the object language (i.e. terms). For example, we can define 'delay' as taking a term
and returning a lambda that takes unit and returns the term, or we could define a 'delay' term

\t : a . \u : unit . t

We generally prefer the metalanguage approach despite the fact that we could share combinators
with the standard library because it makes the generated terms simpler without the need for
a simplifier pass. Also, PLC isn't lazy, so combinators work less well.
-}

delay :: MonadQuote m => PLC.Term PLC.TyName PLC.Name () -> m (PLC.Term PLC.TyName PLC.Name ())
delay body = PLC.LamAbs () <$> liftQuote (freshName () "thunk") <*> liftQuote Unit.getBuiltinUnit <*> pure body

delayType :: MonadQuote m => PLC.Type PLC.TyName () -> m (PLC.Type PLC.TyName ())
delayType orig = PLC.TyFun () <$> liftQuote Unit.getBuiltinUnit <*> pure orig

force :: MonadQuote m => PLC.Term PLC.TyName PLC.Name () -> m (PLC.Term PLC.TyName PLC.Name ())
force thunk = PLC.Apply () thunk <$> liftQuote Unit.getBuiltinUnitval
