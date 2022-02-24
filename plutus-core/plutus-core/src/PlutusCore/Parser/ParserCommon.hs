{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -Wno-deferred-out-of-scope-variables #-}

-- | Common functions for parsers of UPLC, PLC, and PIR.

module PlutusCore.Parser.ParserCommon where

import Data.Char (isAlphaNum)
import Data.Map qualified as M
import Data.Text qualified as T
import PlutusPrelude
import Text.Megaparsec hiding (ParseError, State, parse, some)
import Text.Megaparsec.Char (char, letterChar, space1)
import Text.Megaparsec.Char.Lexer qualified as Lex hiding (hexadecimal)

import Control.Monad.Except
import Control.Monad.State (MonadState (get, put), StateT, evalStateT)
import Data.ByteString.Lazy (ByteString)
import Data.ByteString.Lazy.Internal (unpackChars)
import PlutusCore.Core.Type
import PlutusCore.Error
import PlutusCore.Name
import PlutusCore.Quote
newtype ParserState = ParserState { identifiers :: M.Map T.Text Unique }
    deriving stock (Show)

type Parser =
    ParsecT ParserError T.Text (StateT ParserState Quote)

instance (Stream s, MonadQuote m) => MonadQuote (ParsecT e s m)

initial :: ParserState
initial = ParserState M.empty

-- | Return the unique identifier of a name.
-- If it's not in the current parser state, map the name to a fresh id
-- and add it to the state. Used in the Name parser.
intern :: (MonadState ParserState m, MonadQuote m)
    => T.Text -> m Unique
intern n = do
    st <- get
    case M.lookup n (identifiers st) of
        Just u -> return u
        Nothing -> do
            fresh <- freshUnique
            let identifiers' = M.insert n fresh $ identifiers st
            put $ ParserState identifiers'
            return fresh

parse :: (MonadQuote m, MonadError e m) =>
    Parser a -> String -> T.Text
    -> m a
parse p file str =
    throwingEither
        _ParseErrorBundle --FIXME
        (runQuote $ evalStateT (runParserT p file str) initial)

    --liftEither $ runQuote $ evalStateT (runParserT p file str) initial

-- | Generic parser function.
parseGen :: (MonadError e m, MonadQuote m) => Parser a -> ByteString -> m a
parseGen stuff bs = parse stuff "test" $ (T.pack . unpackChars) bs

-- | Space consumer.
whitespace :: Parser ()
whitespace = Lex.space space1 (Lex.skipLineComment "--") (Lex.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = Lex.lexeme whitespace

symbol :: T.Text -> Parser T.Text
symbol = Lex.symbol whitespace

inParens :: Parser a -> Parser a
inParens = between (symbol "(") (symbol ")")

inBrackets :: Parser a -> Parser a
inBrackets = between (symbol "[") (symbol "]")

inBraces :: Parser a-> Parser a
inBraces = between (symbol "{") (symbol "}")

isIdentifierChar :: Char -> Bool
isIdentifierChar c = isAlphaNum c || c == '_' || c == '\''

-- | Create a parser that matches the input word and returns its source position.
-- This is for attaching source positions to parsed terms/programs.
wordPos ::
    -- | The word to match
    T.Text -> Parser SourcePos
wordPos w = lexeme $ try $ getSourcePos <* symbol w

version :: Parser (Version SourcePos)
version = lexeme $ do
    p <- getSourcePos
    x <- Lex.decimal
    void $ char '.'
    y <- Lex.decimal
    void $ char '.'
    Version p x y <$> Lex.decimal

name :: Parser Name
name = lexeme $ try $ do
    void $ lookAhead letterChar
    str <- takeWhileP (Just "identifier") isIdentifierChar
    Name str <$> intern str

