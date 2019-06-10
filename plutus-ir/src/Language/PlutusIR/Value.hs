{-# LANGUAGE LambdaCase #-}
module Language.PlutusIR.Value (isTermValue) where

import           Language.PlutusIR

-- | Whether the given PIR term is (will compile to) a PLC term value. Very similar to
-- the PLC definition.
isTermValue :: Term tyname name a -> Bool
isTermValue = \case
    LamAbs {} -> True
    Constant {} -> True
    TyAbs _ _ _ t -> isTermValue t
    IWrap _ _ _ t -> isTermValue t
    _ -> False
