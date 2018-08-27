{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE FlexibleInstances       #-}

module Language.PlutusCore.Error ( Error (..)
                                 , IsError (..)
                                 ) where

import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.TypeSynthesis
import           PlutusPrelude

data Error = ParseError ParseError
           | RenameError (RenameError AlexPosn)
           | TypeError (TypeError AlexPosn)
           | NormalizationError (NormalizationError AlexPosn)

class IsError a where

    asError :: a -> Error

    asLeft :: a -> Either Error b
    asLeft = Left . asError

    convertError :: Either a b -> Either Error b
    convertError = first asError

    collectErrors :: (IsError b) => Either a (Either b c) -> Either Error c
    collectErrors (Left x)          = asLeft x
    collectErrors (Right (Left x))  = asLeft x
    collectErrors (Right (Right x)) = Right x

instance IsError Error where
    asError = id

instance IsError ParseError where
    asError = ParseError

instance IsError (RenameError AlexPosn) where
    asError = RenameError

instance IsError (TypeError AlexPosn) where
    asError = TypeError

instance IsError (NormalizationError AlexPosn) where
    asError = NormalizationError

instance Pretty Error where
    pretty (ParseError e)         = pretty e
    pretty (RenameError e)        = pretty e
    pretty (TypeError e)          = pretty e
    pretty (NormalizationError e) = pretty e

instance Debug Error where
    debug (ParseError e)         = pretty e
    debug (RenameError e)        = debug e
    debug (TypeError e)          = debug e
    debug (NormalizationError e) = pretty e
