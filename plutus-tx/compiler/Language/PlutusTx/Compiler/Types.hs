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
import           Control.Monad.State

import qualified Data.List.NonEmpty                     as NE
import qualified Data.Map                               as Map
import qualified Data.Set                               as Set

import qualified Language.Haskell.TH.Syntax             as TH

type BuiltinNameInfo = Map.Map TH.Name GHC.TyThing

-- | Compilation options. Empty currently.
data CompileOptions = CompileOptions {}

data CompileContext = CompileContext {
    ccOpts            :: CompileOptions,
    ccFlags           :: GHC.DynFlags,
    ccBuiltinNameInfo :: BuiltinNameInfo,
    ccScopes          :: ScopeStack,
    ccBlackholed      :: Set.Set GHC.Name
    }

newtype CompileState = CompileState {
    -- See Note [Lazy let-bindings]
    csLazyNames :: Set.Set GHC.Name
    }

-- | A wrapper around 'GHC.Name' with a stable 'Ord' instance. Use this where the ordering
-- will affect the output of the compiler, i.e. when sorting or so on. It's  fine to use
-- 'GHC.Name' if we're just putting them in a 'Set.Set', for example.
--
-- The 'Eq' instance we derive - it's also not stable across builds, but I believe this is only
-- a problem if you compare things from different builds, which we don't do.
newtype LexName = LexName GHC.Name
    deriving Eq

instance Show LexName where
    show (LexName n) = GHC.occNameString $ GHC.occName n

instance Ord LexName where
    compare (LexName n1) (LexName n2) = GHC.stableNameCmp n1 n2

-- See Note [Scopes]
type Compiling m = (Monad m, MonadError CompileError m, MonadQuote m, MonadReader CompileContext m, MonadState CompileState m, MonadDefs LexName () m)

blackhole :: MonadReader CompileContext m => GHC.Name -> m a -> m a
blackhole name = local (\cc -> cc {ccBlackholed=Set.insert name (ccBlackholed cc)})

blackholed :: MonadReader CompileContext m => GHC.Name -> m Bool
blackholed name = do
    CompileContext {ccBlackholed=bh} <- ask
    pure $ Set.member name bh

markLazyName :: MonadState CompileState m => GHC.Name -> m ()
markLazyName name = modify (\s -> s {csLazyNames= Set.insert name (csLazyNames s)})

isLazyName :: MonadState CompileState m => GHC.Name -> m Bool
isLazyName name = do
    CompileState {csLazyNames=ln} <- get
    pure $ Set.member name ln

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
