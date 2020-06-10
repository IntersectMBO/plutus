{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.PlutusCore.Check.Value
    ( isTermValue
    ) where

import           Language.PlutusCore.Core
import           Language.PlutusCore.Error

import           Data.Either

isTermValue :: Term tyname name uni ann -> Bool
isTermValue = isRight . termValue

termValue :: Term tyname name uni ann -> Either (NormCheckError tyname name uni ann) ()
termValue =
    let err t = Left $ BadTerm (termAnn t) t "term value"
    in \case
     IWrap _ _ _ term -> termValue term
     Constant {}        -> pure ()
     TyAbs {}           -> pure ()
     LamAbs {}          -> pure ()
     t@Var{}            -> err t
     t@Apply{}          -> err t
     t@TyInst{}         -> err t
     t@Unwrap{}         -> err t
     t@ApplyBuiltin{}   -> err t
     t@Error{}          -> err t
