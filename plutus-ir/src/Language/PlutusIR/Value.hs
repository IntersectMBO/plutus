{-# LANGUAGE LambdaCase #-}
module Language.PlutusIR.Value (isTermValue) where

import           Language.PlutusIR

-- | Whether the given PIR term is (will compile to) a PLC term value.
isTermValue :: Term tyname name a -> Bool
isTermValue = \case
    -- Let is not a value (will compile into applications and/or type instantiations)
    Let {} -> False
    -- Lambdas and constants are always values
    LamAbs {} -> True
    Constant {} -> True
    Builtin {} -> True
    -- Type abstractions and wraps are values if their bodies are
    TyAbs _ _ _ t -> isTermValue t
    IWrap _ _ _ t -> isTermValue t
    -- All other PLC terms are not values
    Var {} -> False
    Apply {} -> False
    TyInst {} -> False
    Error {} -> False
    Unwrap {} -> False
