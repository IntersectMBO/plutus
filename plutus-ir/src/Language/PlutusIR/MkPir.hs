{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.PlutusIR.MkPir ( module MkPlc
                               , DatatypeDef
                               , mkLet
                               ) where

import           Language.PlutusIR

import           Language.PlutusCore.MkPlc as MkPlc

-- | A datatype definition as a type variable.
type DatatypeDef tyname name a = Def (TyVarDecl tyname a) (Datatype tyname name a)

-- | Make a let binding, unless the list of bindings is empty, in which case just
-- return the underlying term.
mkLet
    :: a
    -> Recursivity
    -> [Binding tyname name a]
    -> Term tyname name a
    -> Term tyname name a
mkLet x r bs t = if null bs then t else Let x r bs t
