{-# LANGUAGE LambdaCase #-}
module Language.PlutusIR.Value (isTermValue) where

import           Language.PlutusIR

-- | Whether the given PIR term is (will compile to) a PLC term value.
isTermValue :: Term tyname name a -> Bool
isTermValue = \case
    -- Let is not a value (will compile into applications and/or type instantiations)
    Let {} -> False
    -- Lambdas, variables, constants, and builtins are always values
    LamAbs {} -> True
    Var {} -> True
    Constant {} -> True
    Builtin {} -> True
    -- Type abstractions and wraps are values if their bodies are
    TyAbs _ _ _ t -> isTermValue t
    Wrap _ _ _ t -> isTermValue t
    x -> isBuiltinValue x

-- Builtins or applications of builtins are also values
isBuiltinValue :: Term tyname name a -> Bool
isBuiltinValue = \case
    Builtin {} -> True
    Apply _ fun _ -> isBuiltinValue fun
    -- All other PLC terms are not values
    _ -> False
