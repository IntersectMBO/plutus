module PlutusIR
  ( -- * AST
    Term (..)
  , progAnn
  , progVer
  , progTerm
  , termSubterms
  , termSubtypes
  , termBindings
  , termAnn
  , bindingAnn
  , Type (..)
  , typeSubtypes
  , Datatype (..)
  , datatypeNameString
  , datatypeSubtypes
  , Kind (..)
  , Recursivity (..)
  , Strictness (..)
  , Binding (..)
  , bindingSubterms
  , bindingSubtypes
  , bindingIds
  , Program (..)
  , applyProgram
  , TyName (..)
  , Name (..)
  , VarDecl (..)
  , TyVarDecl (..)
  , varDeclNameString
  , tyVarDeclNameString
  ) where

import PlutusIR.Core
