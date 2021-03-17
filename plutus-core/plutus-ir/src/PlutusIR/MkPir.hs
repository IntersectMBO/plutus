{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusIR.MkPir ( module MkPlc
                               , DatatypeDef
                               , mkLet
                               ) where

import           PlutusIR

import           PlutusCore.MkPlc   as MkPlc

import qualified Data.List.NonEmpty as NE


-- | A datatype definition as a type variable.
type DatatypeDef tyname name uni fun a = Def (TyVarDecl tyname a) (Datatype tyname name uni fun a)

-- | Make a let binding, unless the list of bindings is empty, in which case just
-- return the underlying term.
mkLet
    :: a
    -> Recursivity
    -> [Binding tyname name uni fun a]
    -> Term tyname name uni fun a
    -> Term tyname name uni fun a
mkLet x r bs t =  case NE.nonEmpty bs of
  Nothing  -> t
  Just bs' -> Let x r bs' t
