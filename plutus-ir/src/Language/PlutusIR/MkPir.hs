{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.PlutusIR.MkPir ( module MkPlc
                               , DatatypeDef
                               , mkLet
                               ) where

import           Language.PlutusIR

import           Language.PlutusCore.MkPlc as MkPlc

import qualified Data.List.NonEmpty        as NE


-- | A datatype definition as a type variable.
type DatatypeDef tyname name uni a = Def (TyVarDecl tyname a) (Datatype tyname name uni a)

-- | Make a let binding, unless the list of bindings is empty, in which case just
-- return the underlying term.
mkLet
    :: a
    -> Recursivity
    -> [Binding tyname name uni a]
    -> Term tyname name uni a
    -> Term tyname name uni a
mkLet x r bs t =  case NE.nonEmpty bs of
  Nothing  -> t;
  Just bs' -> Let x r bs' t
