module PlutusIR (
    -- * AST
    Term (..),
    termSubterms,
    termSubtermsM,
    termSubtypes,
    termSubtypesM,
    termBindings,
    Type (..),
    typeSubtypes,
    Datatype (..),
    datatypeNameString,
    datatypeSubtypes,
    Kind (..),
    Recursivity (..),
    Strictness (..),
    Binding (..),
    bindingSubterms,
    bindingSubtermsM,
    bindingSubtypes,
    bindingIds,
    Program (..),
    applyProgram,
    TyName (..),
    Name (..),
    VarDecl (..),
    TyVarDecl (..),
    varDeclNameString,
    tyVarDeclNameString
    ) where

import           PlutusIR.Core
