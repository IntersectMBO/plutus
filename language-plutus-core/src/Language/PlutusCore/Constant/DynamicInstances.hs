{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.PlutusCore.Constant.DynamicInstances
    () where

import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.StdLib.Data.Unit

-- Encode '()' from Haskell as @all r. r -> r@ from PLC.
instance KnownDynamicBuiltinType () where
    getTypeEncoding _ = getBuiltinUnit

    -- We need this matching, because otherwise Haskell expressions are thrown away rather than being
    -- evaluated and we use 'unsafePerformIO' in multiple places, so we want to compute the '()' just
    -- for side effects the evaluation may cause.
    makeDynamicBuiltin () = Just <$> getBuiltinUnitval

    -- We do not check here that the term is indeed @unitval@. TODO: check.
    readDynamicBuiltin _ _ = Just ()
