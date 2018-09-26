{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types       #-}

module Language.Plutus.CoreToPLC.Types where

import           Language.Plutus.CoreToPLC.Error

import qualified Language.PlutusCore             as PLC
import           Language.PlutusCore.Quote

import qualified GhcPlugins                      as GHC

import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State

import qualified Data.List.NonEmpty              as NE
import qualified Data.Map                        as Map
import qualified Data.Text                       as T

type PLCExpr = PLC.Term PLC.TyName PLC.Name ()
type PLCType = PLC.Type PLC.TyName ()

type ConvError = WithContext T.Text (Error ())

type PrimTerms = Map.Map GHC.Name (Quote PLCExpr)
type PrimTypes = Map.Map GHC.Name (Quote PLCType)

newtype ConversionOptions = ConversionOptions { coCheckValueRestriction :: Bool }

data ConvertingContext = ConvertingContext { ccOpts :: ConversionOptions, ccFlags :: GHC.DynFlags, ccPrimTerms :: PrimTerms, ccPrimTypes :: PrimTypes, ccScopes :: ScopeStack }

data EvalState a = Done | InProgress a
type TypeDefs = Map.Map GHC.Name (EvalState (PLC.TyName ()))
newtype ConvertingState = ConvertingState { csTypeDefs :: TypeDefs }

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
