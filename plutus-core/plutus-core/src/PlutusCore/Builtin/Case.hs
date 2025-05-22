{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators         #-}

module PlutusCore.Builtin.Case where

import PlutusCore.Core.Type (Type, UniOf)
import PlutusCore.Name.Unique

import Data.Text (Text)
import Data.Vector (Vector)
import Universe

class AnnotateCaseBuiltin uni where
    -- | Given a tag for a built-in type and a list of branches, annotate each of the branches with
    -- its expected type or fail if casing on values of the built-in type isn't supported.
    annotateCaseBuiltin
        :: UniOf term ~ uni
        => SomeTypeIn uni
        -> [term]
        -> Either Text [(term, [Type TyName uni ann])]

class UniOf term ~ uni => CaseBuiltin term uni where
    -- | Given a constant with its type tag and a vector of branches, choose the appropriate branch
    -- or fail if the constant doesn't correspond to any of the branches (or casing on constants of
    -- this type isn't supported at all).
    caseBuiltin :: Some (ValueOf uni) -> Vector term -> Either Text term
