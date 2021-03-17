module Scoped where

import           PlutusCore

data ScKind = ScKiStar
            | ScKiFun ScKind ScKind
            deriving Show

data ScType = ScTyVar Integer
           | ScTyFun ScType ScType
           | ScTyPi ScKind ScType
           | ScTyLambda ScKind ScType
           | ScTyApp ScType ScType
           | ScTyCon (Some (TypeIn DefaultUni))
           deriving Show
