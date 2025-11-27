{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Check.Value
  ( isTermValue
  ) where

import PlutusCore.Core
import PlutusCore.Error

import Data.Either

isTermValue :: Term tyname name uni fun ann -> Bool
isTermValue = isRight . termValue

termValue :: Term tyname name uni fun ann -> Either (NormCheckError tyname name uni fun ann) ()
termValue (IWrap _ _ _ term) = termValue term
termValue LamAbs {} = pure ()
termValue TyAbs {} = pure ()
termValue Constant {} = pure ()
termValue t = Left $ BadTerm (termAnn t) t "term value"
