{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Functions for compiling GHC kinds into PlutusCore kinds.
module PlutusTx.Compiler.Kind (compileKind) where

import           PlutusTx.Compiler.Error
import           PlutusTx.Compiler.Types
import           PlutusTx.Compiler.Utils

import qualified GhcPlugins              as GHC

import qualified PlutusCore              as PLC

compileKind :: Compiling uni fun m => GHC.Kind -> m (PLC.Kind ())
compileKind k = withContextM 2 (sdToTxt $ "Compiling kind:" GHC.<+> GHC.ppr k) $ case k of
    -- this is a bit weird because GHC uses 'Type' to represent kinds, so '* -> *' is a 'TyFun'
    (GHC.isLiftedTypeKind -> True)        -> pure $ PLC.Type ()
    (GHC.splitFunTy_maybe -> Just (i, o)) -> PLC.KindArrow () <$> compileKind i <*> compileKind o
    _                                     -> throwSd UnsupportedError $ "Kind:" GHC.<+> GHC.ppr k
