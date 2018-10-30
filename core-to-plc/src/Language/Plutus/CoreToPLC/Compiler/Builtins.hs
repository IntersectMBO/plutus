{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Functions for compiling Plutus Core builtins.
module Language.Plutus.CoreToPLC.Compiler.Builtins where

import qualified Language.Plutus.CoreToPLC.Builtins                  as Builtins
import           Language.Plutus.CoreToPLC.Compiler.Names
import           Language.Plutus.CoreToPLC.Compiler.ValueRestriction
import           Language.Plutus.CoreToPLC.Utils

import qualified Language.PlutusCore                                 as PLC
import           Language.PlutusCore.Quote

import qualified Language.Haskell.TH.Syntax                          as TH

-- Plutus primitives

{- Note [Mapping builtins]
We want the user to be able to call the Plutus builtins as normal Haskell functions.

To do this, we provide a library of such functions, and then make a map from their TH names (which we can
derive from the real function declarations, to be sure they match up), to the implementations. We then
need to do some work in the GHC Core monad to translate those mappings into mappings from Core names.
-}

builtinTermAssociations :: [(TH.Name, Quote (PLC.Term PLC.TyName PLC.Name ()))]
builtinTermAssociations = [
    ('Builtins.concatenate, pure $ instSize haskellIntSize $ mkConstant PLC.Concatenate)
    , ('Builtins.takeByteString, pure $ instSize haskellBSSize $ instSize haskellIntSize $ mkConstant PLC.TakeByteString)
    , ('Builtins.dropByteString, pure $ instSize haskellBSSize $ instSize haskellIntSize $ mkConstant PLC.DropByteString)
    , ('Builtins.sha2_256, pure $ instSize haskellBSSize $ mkConstant PLC.SHA2)
    , ('Builtins.sha3_256, pure $ instSize haskellBSSize $ mkConstant PLC.SHA3)
    , ('Builtins.verifySignature, pure $ instSize haskellBSSize $ instSize haskellBSSize $ instSize haskellBSSize $ mkConstant PLC.VerifySignature)
    , ('Builtins.equalsByteString, pure $ mkBsRel PLC.EqByteString)
    , ('Builtins.txhash, pure $ mkConstant PLC.TxHash)
    , ('Builtins.blocknum, pure $ instSize haskellIntSize $ mkConstant PLC.BlockNum)
    -- we're representing error at the haskell level as a polymorphic function, so do the same here
    , ('Builtins.error, errorFunc)
    ]

builtinTypeAssociations :: [(TH.Name, Quote (PLC.Type PLC.TyName ()))]
builtinTypeAssociations = [
    (''Builtins.ByteString, pure $ appSize haskellBSSize $ PLC.TyBuiltin () PLC.TyByteString)
    ]

-- | The function 'error :: forall a . () -> a'.
errorFunc :: Quote (PLC.Term PLC.TyName PLC.Name ())
errorFunc = do
    n <- freshTyName () "e"
    -- see Note [Value restriction]
    mangleTyAbs $ PLC.TyAbs () n (PLC.Type ()) (PLC.Error () (PLC.TyVar () n))

-- | The type 'forall a. () -> a'.
errorTy :: Quote (PLC.Type PLC.TyName ())
errorTy = do
    tyname <- safeFreshTyName "a"
    mangleTyForall $ PLC.TyForall () tyname (PLC.Type ()) (PLC.TyVar () tyname)
