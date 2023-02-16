{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecursiveDo       #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Common functions for parsers of UPLC, PLC, and PIR.

module PlutusCore.Parser.ParserCommon where

import Control.Monad.Except
import Control.Monad.State (MonadState (get, put), StateT, evalStateT)
import Data.Char (isAlphaNum)
import Data.Map qualified as M
import Data.Text qualified as T
import Text.Megaparsec hiding (ParseError, State, parse, some)
import Text.Megaparsec.Char (char, letterChar, space1)
import Text.Megaparsec.Char.Lexer qualified as Lex hiding (hexadecimal)

import PlutusCore.Annotation
import PlutusCore.Core.Type
import PlutusCore.Error
import PlutusCore.Name
import PlutusCore.Quote

{- Note [Whitespace invariant]
Every top-level 'Parser' must consume all whitespace after the thing that it parses, hence make
sure to enclose every 'Parser' that doesn't consume trailing whitespce (e.g. 'takeWhileP',
'manyTill', 'Lex.decimal' etc) in a call to 'lexeme'.
-}

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

parse :: (AsParserErrorBundle e, MonadError e m, MonadQuote m) =>
    Parser a -> String -> T.Text -> m a
parse p file str = do
    let res = fmap toErrorB (evalStateT (runParserT p file str) initial)
    throwingEither _ParserErrorBundle =<< liftQuote res

toErrorB :: Either (ParseErrorBundle T.Text ParserError) a -> Either ParserErrorBundle a
toErrorB (Left err) = Left $ ParseErrorB err
toErrorB (Right a)  = Right a

-- | Generic parser function in which the file path is just "test".
parseGen :: (AsParserErrorBundle e, MonadError e m, MonadQuote m) => Parser a -> T.Text -> m a
parseGen stuff = parse stuff "test"

-- | Space consumer.
whitespace :: Parser ()
whitespace = Lex.space space1 (Lex.skipLineComment "--") (Lex.skipBlockCommentNested "{-" "-}")

leadingWhitespace :: Parser a -> Parser a
leadingWhitespace = (whitespace *>)

trailingWhitespace :: Parser a -> Parser a
trailingWhitespace = (<* whitespace)

-- | Returns a parser for @a@ by calling the supplied function on the starting
-- and ending positions of @a@.
--
-- The supplied function should usually return a parser that does /not/ consume trailing
-- whitespaces. Otherwise, the end position will be the first character after the
-- trailing whitespaces.
withSpan' :: (SrcSpan -> Parser a) -> Parser a
withSpan' f = mdo
  start <- getSourcePos
  res <- f sp
  end <- getSourcePos
  let sp = toSrcSpan start end
  pure res

-- | Like `withSpan'`, but the result parser consumes whitespaces.
--
-- @withSpan = (<* whitespace) . withSpan'
withSpan :: (SrcSpan -> Parser a) -> Parser a
withSpan = (<* whitespace) . withSpan'

lexeme :: Parser a -> Parser a
lexeme = Lex.lexeme whitespace

symbol :: T.Text -> Parser T.Text
symbol = Lex.symbol whitespace

inParens :: Parser a -> Parser a
inParens = between (symbol "(") (char ')')

inBrackets :: Parser a -> Parser a
inBrackets = between (symbol "[") (char ']')

inBraces :: Parser a -> Parser a
inBraces = between (symbol "{") (char '}')

isIdentifierChar :: Char -> Bool
isIdentifierChar c = isAlphaNum c || c == '_' || c == '\''

toSrcSpan :: SourcePos -> SourcePos -> SrcSpan
toSrcSpan start end =
    SrcSpan
        { srcSpanFile = sourceName start
        , srcSpanSLine = unPos (sourceLine start)
        , srcSpanSCol = unPos (sourceColumn start)
        , srcSpanELine = unPos (sourceLine end)
        , srcSpanECol = unPos (sourceColumn end)
        }

version :: Parser Version
version = trailingWhitespace $ do
    x <- Lex.decimal
    void $ char '.'
    y <- Lex.decimal
    void $ char '.'
    Version x y <$> Lex.decimal

-- | Parses a `Name`. Does not consume leading or trailing whitespaces.
name :: Parser Name
name = try $ do
    void $ lookAhead letterChar
    str <- takeWhileP (Just "identifier") isIdentifierChar
    Name str <$> intern str
