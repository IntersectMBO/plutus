{-# LANGUAGE ConstrainedClassMethods #-}
{-# LANGUAGE DeriveAnyClass          #-}
{-# LANGUAGE FlexibleInstances       #-}

module Language.PlutusCore.Error ( Error (..)
                                 , IsError (..)
                                 ) where

import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Normalize
import           Language.PlutusCore.PrettyCfg
import           Language.PlutusCore.Renamer
import           Language.PlutusCore.TypeSynthesis
import           PlutusPrelude

data Error a = ParseError (ParseError a)
             | RenameError (RenameError a)
             | TypeError (TypeError a)
             | NormalizationError (NormalizationError a)
             deriving (Generic, NFData)

class IsError f where

    asError :: f a -> Error a

    asLeft :: f a -> Either (Error a) b
    asLeft = Left . asError

    convertError :: Either (f a) b -> Either (Error a) b
    convertError = first asError

    collectErrors :: (IsError g) => Either (f a) (Either (g a) b) -> Either (Error a) b
    collectErrors (Left x)          = asLeft x
    collectErrors (Right (Left x))  = asLeft x
    collectErrors (Right (Right x)) = Right x

instance IsError Error where
    asError = id

instance IsError ParseError where
    asError = ParseError

instance IsError RenameError where
    asError = RenameError

instance IsError TypeError where
    asError = TypeError

instance IsError NormalizationError where
    asError = NormalizationError

instance (PrettyCfg a) => PrettyCfg (Error a) where
    prettyCfg cfg (ParseError e)         = prettyCfg cfg e
    prettyCfg cfg (RenameError e)        = prettyCfg cfg e
    prettyCfg cfg (TypeError e)          = prettyCfg cfg e
    prettyCfg cfg (NormalizationError e) = prettyCfg cfg e
