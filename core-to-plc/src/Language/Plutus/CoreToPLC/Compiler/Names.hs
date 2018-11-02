{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Functions for compiling GHC names into Plutus Core names.
module Language.Plutus.CoreToPLC.Compiler.Names where

import           Language.Plutus.CoreToPLC.Compiler.Kind
import {-# SOURCE #-} Language.Plutus.CoreToPLC.Compiler.Type
import           Language.Plutus.CoreToPLC.Compiler.Types
import           Language.Plutus.CoreToPLC.PLCTypes
import           Language.Plutus.CoreToPLC.Utils

import qualified GhcPlugins                               as GHC

import qualified Language.PlutusCore                      as PLC
import qualified Language.PlutusCore.MkPlc                as PLC
import           Language.PlutusCore.Quote

import           Data.Char
import qualified Data.List.NonEmpty                       as NE
import qualified Data.Map                                 as Map

lookupName :: Scope -> GHC.Name -> Maybe PLCVar
lookupName (Scope ns _) n = Map.lookup n ns

{- Note [PLC names]
We convert names from Haskell names quite frequently here, but PLC admits a much
smaller set of valid identifiers. We compromise by mangling the identifier, but
in the long run it would be nice to have a more principled encoding so we can
support unicode identifiers as well.
-}

safeFreshName :: MonadQuote m => String -> m (PLC.Name ())
safeFreshName s
    -- some special cases
    | s == ":" = safeFreshName "cons"
    | s == "[]" = safeFreshName "list"
    | s == "()" = safeFreshName "unit"
    | otherwise =
          let
              -- See Note [PLC names]
              -- first strip out disallowed characters
              stripped = filter (\c -> isLetter c || isDigit c || c == '_' || c == '`') s
              -- now fix up some other bits
              fixed = case stripped of
                -- empty name, just put something to mark that
                []      -> "bad_name"
                -- can't start with these
                ('`':_) -> "p" ++ stripped
                ('_':_) -> "p" ++ stripped
                n       -> n
          in liftQuote $ freshName () $ strToBs fixed

convNameFresh :: MonadQuote m => GHC.Name -> m (PLC.Name ())
convNameFresh n = safeFreshName $ GHC.getOccString n

convVarFresh :: Converting m => GHC.Var -> m PLCVar
convVarFresh v = do
    t' <- convType $ GHC.varType v
    n' <- convNameFresh $ GHC.getName v
    pure $ PLC.VarDecl () n' t'

lookupTyName :: Scope -> GHC.Name -> Maybe PLCTyVar
lookupTyName (Scope _ tyns) n = Map.lookup n tyns

safeFreshTyName :: MonadQuote m => String -> m (PLC.TyName ())
safeFreshTyName s = PLC.TyName <$> safeFreshName s

convTyNameFresh :: MonadQuote m => GHC.Name -> m (PLC.TyName ())
convTyNameFresh n = PLC.TyName <$> convNameFresh n

convTyVarFresh :: Converting m => GHC.TyVar -> m PLCTyVar
convTyVarFresh v = do
    k' <- convKind $ GHC.tyVarKind v
    t' <- convTyNameFresh $ GHC.getName v
    pure $ PLC.TyVarDecl () t' k'

pushName :: GHC.Name -> PLCVar-> ScopeStack -> ScopeStack
pushName ghcName n stack = let Scope ns tyns = NE.head stack in Scope (Map.insert ghcName n ns) tyns NE.<| stack

pushTyName :: GHC.Name -> PLCTyVar -> ScopeStack -> ScopeStack
pushTyName ghcName n stack = let Scope ns tyns = NE.head stack in Scope ns (Map.insert ghcName n tyns) NE.<| stack
