{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RecursiveDo #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Common functions for parsers of UPLC, PLC, and PIR.
module PlutusCore.Parser.ParserCommon where

import Control.Monad (when)
import Control.Monad.Except
import Control.Monad.Reader (ReaderT, ask, local, runReaderT)
import Control.Monad.State (StateT, evalStateT)
import Data.Map qualified as M
import Data.Text (Text)
import Data.Text qualified as Text
import Text.Megaparsec hiding (ParseError, State, parse, some)
import Text.Megaparsec.Char (char, space1)
import Text.Megaparsec.Char.Lexer qualified as Lex hiding (hexadecimal)

import Control.Monad.State.Class (MonadState, get, put)
import PlutusCore.Annotation
import PlutusCore.Core.Type
import PlutusCore.Error
import PlutusCore.Name.Unique
  ( Name (..)
  , Unique (..)
  , isIdentifierChar
  , isIdentifierStartingChar
  , isQuotedIdentifierChar
  )
import PlutusCore.Quote

{- Note [Whitespace invariant]
Every top-level 'Parser' must consume all whitespace after the thing that it parses, hence make
sure to enclose every 'Parser' that doesn't consume trailing whitespce (e.g. 'takeWhileP',
'manyTill', 'Lex.decimal' etc) in a call to 'lexeme'.
-}

newtype ParserState = ParserState {identifiers :: M.Map Text Unique}
  deriving stock (Show)

type Parser =
  ParsecT ParserError Text (StateT ParserState (ReaderT (Maybe Version) Quote))

instance (Stream s, MonadQuote m) => MonadQuote (ParsecT e s m)

initial :: ParserState
initial = ParserState M.empty

-- | Get the version of the program being parsed, if we know it.
getVersion :: Parser (Maybe Version)
getVersion = ask

-- | Set the version of the program being parsed.
withVersion :: Version -> Parser a -> Parser a
withVersion v = local (const $ Just v)

{-| Run an action conditionally based on a predicate on the version.
If we don't know the version then the predicate is assumed to be
false, i.e. we act if we _know_ the predicate is satisfied. -}
whenVersion :: (Version -> Bool) -> Parser () -> Parser ()
whenVersion p act = do
  mv <- getVersion
  case mv of
    Nothing -> pure ()
    Just v -> when (p v) act

parse
  :: (MonadError ParserErrorBundle m, MonadQuote m)
  => Parser a
  -> String
  -> Text
  -> m a
parse p file str = do
  let res = fmap toErrorB (runReaderT (evalStateT (runParserT p file str) initial) Nothing)
  liftEither =<< liftQuote res

toErrorB :: Either (ParseErrorBundle Text ParserError) a -> Either ParserErrorBundle a
toErrorB (Left err) = Left $ ParseErrorB err
toErrorB (Right a) = Right a

-- | Generic parser function in which the file path is just "test".
parseGen :: (MonadError ParserErrorBundle m, MonadQuote m) => Parser a -> Text -> m a
parseGen stuff = parse stuff "test"

-- | Space consumer.
whitespace :: Parser ()
whitespace = Lex.space space1 (Lex.skipLineComment "--") (Lex.skipBlockCommentNested "{-" "-}")

leadingWhitespace :: Parser a -> Parser a
leadingWhitespace = (whitespace *>)

trailingWhitespace :: Parser a -> Parser a
trailingWhitespace = (<* whitespace)

-- This is samething from @Text.Megaparsec.Stream@.
reachOffsetNoLine'
  :: forall s
   . Stream s
  => (Int -> s -> (Tokens s, s))
  -- ^ How to split input stream at given offset
  -> (forall b. (b -> Token s -> b) -> b -> Tokens s -> b)
  -- ^ How to fold over input stream
  -> (Token s, Token s)
  -- ^ Newline token and tab token
  -> (Token s -> Pos)
  {-^ Offset to reach
  | Increment in column position for a token -}
  -> Int
  -> PosState s
  -- ^ Initial 'PosState' to use
  -> PosState s
  -- ^ Updated 'PosState'
reachOffsetNoLine'
  splitAt'
  foldl''
  (newlineTok, tabTok)
  columnIncrement
  o
  PosState {..} =
    ( PosState
        { pstateInput = post
        , pstateOffset = max pstateOffset o
        , pstateSourcePos = spos
        , pstateTabWidth = pstateTabWidth
        , pstateLinePrefix = pstateLinePrefix
        }
    )
    where
      spos = foldl'' go pstateSourcePos pre
      (pre, post) = splitAt' (o - pstateOffset) pstateInput
      go (SourcePos n l c) ch =
        let c' = unPos c
            w = unPos pstateTabWidth
         in if
              | ch == newlineTok ->
                  SourcePos n (l <> pos1) pos1
              | ch == tabTok ->
                  SourcePos n l (mkPos $ c' + w - ((c' - 1) `rem` w))
              | otherwise ->
                  SourcePos n l (c <> columnIncrement ch)
{-# INLINE reachOffsetNoLine' #-}

getSourcePos' :: MonadParsec e Text m => m SourcePos
getSourcePos' = do
  st <- getParserState
  let
    pst =
      reachOffsetNoLine'
        Text.splitAt
        Text.foldl'
        ('\n', '\t')
        (const pos1)
        (stateOffset st)
        (statePosState st)
  setParserState st {statePosState = pst}
  return (pstateSourcePos pst)

{-| Returns a parser for @a@ by calling the supplied function on the starting
and ending positions of @a@.

The supplied function should usually return a parser that does /not/ consume trailing
whitespaces. Otherwise, the end position will be the first character after the
trailing whitespaces. -}
withSpan' :: (SrcSpan -> Parser a) -> Parser a
withSpan' f = mdo
  start <- getSourcePos'
  res <- f sp
  end <- getSourcePos'
  let sp = toSrcSpan start end
  pure res

{-| Like `withSpan'`, but the result parser consumes whitespaces.

@withSpan = (<* whitespace) . withSpan'@ -}
withSpan :: (SrcSpan -> Parser a) -> Parser a
withSpan = (<* whitespace) . withSpan'

lexeme :: Parser a -> Parser a
lexeme = Lex.lexeme whitespace

symbol :: Text -> Parser Text
symbol = Lex.symbol whitespace

inParens :: Parser a -> Parser a
inParens = between (symbol "(") (char ')')

inBrackets :: Parser a -> Parser a
inBrackets = between (symbol "[") (char ']')

inBraces :: Parser a -> Parser a
inBraces = between (symbol "{") (char '}')

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
  _ <- char '.'
  y <- Lex.decimal
  _ <- char '.'
  Version x y <$> Lex.decimal

-- | Parses a `Name`. Does not consume leading or trailing whitespaces.
name :: Parser Name
name = try $ parseUnquoted <|> parseQuoted
  where
    parseUnquoted :: Parser Name
    parseUnquoted = do
      _ <- lookAhead (satisfy isIdentifierStartingChar)
      str <- takeWhileP (Just "identifier-unquoted") isIdentifierChar
      Name str <$> uniqueSuffix str

    parseQuoted :: Parser Name
    parseQuoted = do
      _ <- char '`'
      _ <- lookAhead (satisfy isQuotedIdentifierChar)
      str <- takeWhileP (Just "identifier-quoted") isQuotedIdentifierChar
      _ <- char '`'
      Name str <$> uniqueSuffix str

    -- Tries to parse a `Unique` value.
    -- If it fails then looks up the `Unique` value for the given name.
    -- If lookup fails too then generates a fresh `Unique` value.
    uniqueSuffix :: Text -> Parser Unique
    uniqueSuffix nameStr = try (Unique <$> (char '-' *> Lex.decimal)) <|> uniqueForName nameStr

    -- Return the unique identifier of a name.
    -- If it's not in the current parser state, map the name to a fresh id and add it to the state.
    uniqueForName :: (MonadState ParserState m, MonadQuote m) => Text -> m Unique
    uniqueForName nameStr = do
      parserState <- get
      case M.lookup nameStr (identifiers parserState) of
        Just u -> pure u
        Nothing -> do
          fresh <- freshUnique
          put $ ParserState $ M.insert nameStr fresh $ identifiers parserState
          pure fresh
