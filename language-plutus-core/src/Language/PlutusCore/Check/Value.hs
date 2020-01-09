{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.Check.Value
    ( isTermValue
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.Error

import           Data.Either

isTermValue :: Term tyname name ann -> Bool
isTermValue = isRight . termValue

termValue :: Term tyname name ann -> Either (NormCheckError tyname name ann) ()
termValue (IWrap _ _ _ term) = termValue term
termValue LamAbs {}          = pure ()
termValue TyAbs {}           = pure ()
termValue Constant {}        = pure ()
termValue t                  = Left $ BadTerm (termLoc t) t "term value"
