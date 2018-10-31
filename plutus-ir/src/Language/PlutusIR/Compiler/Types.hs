{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
module Language.PlutusIR.Compiler.Types where

import           Language.PlutusIR.Compiler.Error

import           Control.Monad.Except

import           Language.PlutusCore.Quote

type Compiling m = (Monad m, MonadError CompError m, MonadQuote m)

runCompiling :: QuoteT (Except CompError) a -> Either CompError a
runCompiling = runExcept . runQuoteT

-- | A definition. Pretty much just a pair with more descriptive names.
data Def var val = Def { defVar::var, defVal::val}
