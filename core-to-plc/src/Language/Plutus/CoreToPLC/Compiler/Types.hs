{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Rank2Types        #-}

module Language.Plutus.CoreToPLC.Compiler.Types where

import           Language.Plutus.CoreToPLC.Compiler.Error
import           Language.Plutus.CoreToPLC.PIRTypes
import           Language.Plutus.CoreToPLC.PLCTypes

import           Language.PlutusCore.Quote

import qualified GhcPlugins                               as GHC

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State

import qualified Data.List.NonEmpty                       as NE
import qualified Data.Map                                 as Map
import qualified Data.Set                                 as Set

import qualified Language.Haskell.TH.Syntax               as TH

type BuiltinNameInfo = Map.Map TH.Name GHC.TyThing

newtype ConversionOptions = ConversionOptions { coCheckValueRestriction :: Bool }

data ConvertingContext = ConvertingContext {
    ccOpts            :: ConversionOptions,
    ccFlags           :: GHC.DynFlags,
    ccBuiltinNameInfo :: BuiltinNameInfo,
    ccScopes          :: ScopeStack
    }

type DefMap key def = Map.Map key (def, [key])

data ConvertingState = ConvertingState {
    csDefs    :: DefMap GHC.Name PIRBinding,
    csAliases :: Set.Set GHC.Name
    }

defs :: Lens' ConvertingState (DefMap GHC.Name PIRBinding)
defs = lens g s where
    g = csDefs
    s cs tds = cs { csDefs = tds }

aliases :: Lens' ConvertingState (Set.Set GHC.Name)
aliases = lens g s where
    g = csAliases
    s cs tds = cs { csAliases = tds }

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

data Scope = Scope (Map.Map GHC.Name PLCVar) (Map.Map GHC.Name PLCTyVar)
type ScopeStack = NE.NonEmpty Scope

initialScopeStack :: ScopeStack
initialScopeStack = pure $ Scope Map.empty Map.empty
