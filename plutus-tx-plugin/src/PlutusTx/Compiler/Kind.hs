-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

-- | Functions for compiling GHC kinds into PlutusCore kinds.
module PlutusTx.Compiler.Kind (compileKind) where

import PlutusTx.Compiler.Error
import PlutusTx.Compiler.Trace
import PlutusTx.Compiler.Types
import PlutusTx.Compiler.Utils

import GHC.Plugins qualified as GHC

import PlutusCore qualified as PLC

compileKind :: Compiling uni fun m ann => GHC.Kind -> m (PLC.Kind ())
compileKind k = traceCompilation 2 ("Compiling kind:" GHC.<+> GHC.ppr k) $ case k of
  -- this is a bit weird because GHC uses 'Type' to represent kinds, so '* -> *' is a 'TyFun'
  (GHC.isLiftedTypeKind -> True) -> pure $ PLC.Type ()
  (GHC.splitFunTy_maybe -> Just r) -> case r of
    (_t, _m, i, o) -> PLC.KindArrow () <$> compileKind i <*> compileKind o
  -- Ignore type binders for runtime rep variables, see Note [Runtime reps]
  (GHC.splitForAllTyCoVar_maybe -> Just (tvar, ty)) | (GHC.isRuntimeRepTy . GHC.varType) tvar -> compileKind ty
  -- Interpret 'TYPE rep' as 'TYPE LiftedRep', for any rep, see Note [Runtime reps]
  (GHC.isTypeLikeKind -> True) -> pure $ PLC.Type ()
  _ -> throwSd UnsupportedError $ "Kind:" GHC.<+> (GHC.ppr k)
