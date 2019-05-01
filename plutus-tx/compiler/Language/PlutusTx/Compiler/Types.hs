{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Rank2Types        #-}

module Language.PlutusTx.Compiler.Types where

import           Language.PlutusTx.Compiler.Error
import           Language.PlutusTx.PLCTypes

import           Language.PlutusIR.Compiler.Definitions

import           Language.PlutusCore.Quote

import qualified GhcPlugins                             as GHC

import           Control.Monad.Except
import           Control.Monad.Reader

import qualified Data.List.NonEmpty                     as NE
import qualified Data.Map                               as Map
import qualified Data.Set                               as Set

import qualified Language.Haskell.TH.Syntax             as TH

type BuiltinNameInfo = Map.Map TH.Name GHC.TyThing

newtype ConversionOptions = ConversionOptions { coCheckValueRestriction :: Bool }

data ConvertingContext = ConvertingContext {
    ccOpts            :: ConversionOptions,
    ccFlags           :: GHC.DynFlags,
    ccBuiltinNameInfo :: BuiltinNameInfo,
    ccScopes          :: ScopeStack,
    ccBlackholed      :: Set.Set GHC.Name
    }

-- See Note [Scopes]
type Converting m = (Monad m, MonadError ConvError m, MonadQuote m, MonadReader ConvertingContext m, MonadDefs GHC.Name () m)

blackhole :: MonadReader ConvertingContext m => GHC.Name -> m a -> m a
blackhole name = local (\cc -> cc {ccBlackholed=Set.insert name (ccBlackholed cc)})

blackholed :: MonadReader ConvertingContext m => GHC.Name -> m Bool
blackholed name = do
    ConvertingContext {ccBlackholed=bh} <- ask
    pure $ Set.member name bh

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
