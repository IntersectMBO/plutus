{-# LANGUAGE OverloadedStrings #-}
module Language.PlutusCore.Check.Value
    ( isTermValue
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.Error

import           Data.Either

isTermValue :: Term tyname name uni fun ann -> Bool
isTermValue = isRight . termValue

termValue :: Term tyname name uni fun ann -> Either (NormCheckError tyname name uni fun ann) ()
termValue (IWrap _ _ _ term) = termValue term
termValue LamAbs {}          = pure ()
termValue TyAbs {}           = pure ()
termValue Constant {}        = pure ()
termValue t                  = Left $ BadTerm (toAnnotation t) t "term value"
