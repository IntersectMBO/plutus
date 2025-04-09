{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators         #-}

module PlutusCore.Builtin.Case where

import PlutusCore.Core.Type (Type, UniOf)
import PlutusCore.Name.Unique

import Data.Vector (Vector)
import Universe

class AnnotateCaseBuiltin uni where
    annotateCaseBuiltin
        :: UniOf term ~ uni
        => SomeTypeIn uni
        -> [term]
        -> Either () [(term, [Type TyName uni ann])]

class UniOf term ~ uni => CaseBuiltin term uni where
    caseBuiltin :: Some (ValueOf uni) -> Vector term -> Either () term
