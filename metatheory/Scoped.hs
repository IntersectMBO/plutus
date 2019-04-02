module Scoped where

import           Language.PlutusCore

data ScKind = ScKiStar
            | ScKiSize
            | ScKiFun ScKind ScKind
            deriving Show

data ScType = ScTyVar Integer
           | ScTyFun ScType ScType
           | ScTyPi ScKind ScType
           | ScTyLambda ScKind ScType
           | ScTyApp ScType ScType
           | ScTyCon TypeBuiltin
           | ScTySize Integer
           deriving Show
