-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Functions for compiling GHC kinds into PlutusCore kinds.
module PlutusTx.Compiler.Kind (compileKind) where

import PlutusTx.Compiler.Error
import PlutusTx.Compiler.Types
import PlutusTx.Compiler.Utils

import GHC.Plugins qualified as GHC

import PlutusCore qualified as PLC

compileKind :: Compiling uni fun m ann => GHC.Kind -> m (PLC.Kind ())
compileKind k = withContextM 2 (sdToTxt $ "Compiling kind:" GHC.<+> GHC.ppr k) $ case k of
    -- this is a bit weird because GHC uses 'Type' to represent kinds, so '* -> *' is a 'TyFun'
    (GHC.isLiftedTypeKind -> True)         -> pure $ PLC.Type ()
    (GHC.splitFunTy_maybe -> Just (_m, i, o))  -> PLC.KindArrow () <$> compileKind i <*> compileKind o
    -- We match on the forall type with 'RuntimeRep' type variable
    -- to handle '(#, #)' kind and catch 'TYPE rep' with 'classifiesTypeWithValues'
    -- to match it to a type, see Note [Unboxed tuples]
    (GHC.splitForAllTyCoVar_maybe -> Just (tvar, ty)) | (GHC.isRuntimeRepTy . GHC.varType) tvar -> compileKind ty
    (GHC.classifiesTypeWithValues -> True) -> pure $ PLC.Type ()
    _                                      -> throwSd UnsupportedError $ "Kind:" GHC.<+> (GHC.ppr k)
