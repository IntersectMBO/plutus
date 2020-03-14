{-# LANGUAGE LambdaCase #-}
module Language.PlutusIR.Value (isTermValue) where

import           Language.PlutusIR

-- | Whether the given PIR term is (will compile to) a PLC term value. Very similar to
-- the PLC definition.
isTermValue :: Term tyname name uni a -> Bool
isTermValue = \case
    LamAbs {} -> True
    TyAbs {} -> True
    Constant {} -> True
    IWrap _ _ _ t -> isTermValue t
    _ -> False
