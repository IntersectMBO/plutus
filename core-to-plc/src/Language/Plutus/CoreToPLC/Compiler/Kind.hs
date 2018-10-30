{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Functions for compiling GHC kinds into PlutusCore kinds.
module Language.Plutus.CoreToPLC.Compiler.Kind (convKind) where

import           Language.Plutus.CoreToPLC.Compiler.Types
import           Language.Plutus.CoreToPLC.Compiler.Utils
import           Language.Plutus.CoreToPLC.Error

import qualified GhcPlugins                               as GHC
import qualified Kind                                     as GHC

import qualified Language.PlutusCore                      as PLC

convKind :: Converting m => GHC.Kind -> m (PLC.Kind ())
convKind k = withContextM (sdToTxt $ "Converting kind:" GHC.<+> GHC.ppr k) $ case k of
    -- this is a bit weird because GHC uses 'Type' to represent kinds, so '* -> *' is a 'TyFun'
    (GHC.isStarKind -> True)              -> pure $ PLC.Type ()
    (GHC.splitFunTy_maybe -> Just (i, o)) -> PLC.KindArrow () <$> convKind i <*> convKind o
    _                                     -> throwSd UnsupportedError $ "Kind:" GHC.<+> GHC.ppr k
