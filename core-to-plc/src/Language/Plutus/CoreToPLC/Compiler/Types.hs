{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types       #-}

module Language.Plutus.CoreToPLC.Compiler.Types where

import           Language.Plutus.CoreToPLC.Compiler.Definitions
import           Language.Plutus.CoreToPLC.Error
import           Language.Plutus.CoreToPLC.PLCTypes

import qualified Language.PlutusCore                            as PLC
import           Language.PlutusCore.Quote

import qualified GhcPlugins                                     as GHC

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State

import qualified Data.List.NonEmpty                             as NE
import qualified Data.Map                                       as Map
import           Lens.Micro

type PrimTerms = Map.Map GHC.Name (Quote PLCTerm)
type PrimTypes = Map.Map GHC.Name (Quote PLCType)

newtype ConversionOptions = ConversionOptions { coCheckValueRestriction :: Bool }

data ConvertingContext = ConvertingContext {
    ccOpts      :: ConversionOptions,
    ccFlags     :: GHC.DynFlags,
    ccPrimTerms :: PrimTerms,
    ccPrimTypes :: PrimTypes,
    ccScopes    :: ScopeStack
    }

data ConvertingState = ConvertingState {
    csTypeDefs :: DefMap GHC.Name TypeDef,
    csTermDefs :: DefMap GHC.Name TermDef
    }

typeDefs :: Lens' ConvertingState (DefMap GHC.Name TypeDef)
typeDefs = lens g s where
    g = csTypeDefs
    s cs tds = cs { csTypeDefs = tds }

termDefs :: Lens' ConvertingState (DefMap GHC.Name TermDef)
termDefs = lens g s where
    g = csTermDefs
    s cs tds = cs { csTermDefs = tds }

-- See Note [Scopes]
type Converting m = (Monad m, MonadError ConvError m, MonadQuote m, MonadReader ConvertingContext m, MonadState ConvertingState m)

runConverting :: ConvertingContext -> ConvertingState -> ReaderT ConvertingContext (StateT ConvertingState (QuoteT (Except ConvError))) a -> Either ConvError a
runConverting context initialState = runExcept . runQuoteT . flip evalStateT initialState . flip runReaderT context

{- Note [Scopes]
We need a notion of scope, because we have to make sure that if we convert a GHC
Var into a variable, then we always convert it into the same variable, while also making
sure that if we encounter multiple things with the same name we produce fresh variables
appropriately.

So we have the usual mechanism of carrying around a stack of scopes.
-}

data Scope = Scope (Map.Map GHC.Name (PLC.Name ())) (Map.Map GHC.Name (PLC.TyName ()))
type ScopeStack = NE.NonEmpty Scope

initialScopeStack :: ScopeStack
initialScopeStack = pure $ Scope Map.empty Map.empty
