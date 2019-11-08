module Language.PlutusCore.Parser where

import           Control.Monad.Except
import qualified Data.ByteString.Lazy      as BSL
import           Language.PlutusCore.Error
import           Language.PlutusCore.Lexer
import           Language.PlutusCore.Name
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type

-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m) => BSL.ByteString -> m (Program TyName Name uni AlexPosn)
parseProgram str = undefined -- mapParseRun (parseST str)

-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m) => BSL.ByteString -> m (Term TyName Name uni AlexPosn)
parseTerm str = undefined -- mapParseRun (parseTermST str)

-- | Parse a PLC type. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseType :: (AsParseError e AlexPosn, MonadError e m, MonadQuote m) => BSL.ByteString -> m (Type TyName uni AlexPosn)
parseType str = undefined -- mapParseRun (parseTypeST str)
