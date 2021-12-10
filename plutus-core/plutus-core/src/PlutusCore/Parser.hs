{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module PlutusCore.Parser
    ( parseProgram
    , parseTerm
    , parseType
    , ParseError(..)
    , IdentifierState
    , emptyIdentifierState
    ) where

import PlutusCore.Constant.Typed
import PlutusCore.Core
import PlutusCore.Core.Type
import PlutusCore.Default
import PlutusCore.Error
import PlutusCore.Mark
import PlutusCore.MkPlc (mkConstant, mkTyBuiltin)
import PlutusCore.Name
import PlutusCore.Parsable
import PlutusCore.Parser.Type
import PlutusCore.Quote
import PlutusPrelude
import Universe

import Control.Monad.Except
import Control.Monad.State
import Data.ByteString.Lazy (ByteString)
import Data.List.NonEmpty qualified as NE
import Data.Map qualified
import Data.Proxy
import Data.Text qualified as T
import Text.Megaparsec (SourcePos)

-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram :: (MonadError e m, MonadQuote m) => ByteString -> m (Program TyName Name DefaultUni DefaultFun SourcePos)
parseProgram str = undefined
-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm :: (MonadError e m, MonadQuote m) => ByteString -> m (Term TyName Name DefaultUni DefaultFun SourcePos)
parseTerm str = undefined

-- | Parse a PLC type. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseType :: ByteString -> m (Type TyName DefaultUni SourcePos)
parseType str = undefined
