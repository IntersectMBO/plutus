{-# LANGUAGE LambdaCase #-}
module Language.PlutusIR.Value (isTermValue) where

import           Language.PlutusIR

-- | Whether the given PIR term is (will compile to) a PLC term value. Very similar to
-- the PLC definition. Crucially, evaluating a value should return the value immediately,
-- and it should not be possible for it to loop or throw error.
isTermValue :: Term tyname name uni a -> Bool
isTermValue = \case
    LamAbs {} -> True
    TyAbs {} -> True
    Constant {} -> True
    -- Variables are values: they can only refer to entries in the environment, which
    -- are always values
    Var {} -> True
    IWrap _ _ _ t -> isTermValue t
    _ -> False
