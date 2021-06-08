{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

-- | Common functions for parsers of UPLC, PLC, and PIR.

module PlutusCore.ParserCommon where

import           Data.Char                  (isAlphaNum)
import qualified Data.Map                   as M
import qualified Data.Text                  as T
import           ErrorCode                  (ErrorCode (ErrorCode), HasErrorCode (..))
import qualified PlutusCore                 as PLC
import qualified PlutusCore.Parsable        as PLC
import           PlutusPrelude
import           Text.Megaparsec            hiding (ParseError, State, parse)
import qualified Text.Megaparsec            as Parsec
import           Text.Megaparsec.Char       (char, letterChar, space1, string)
import qualified Text.Megaparsec.Char.Lexer as Lex

import           Control.Monad.State        (MonadState (get, put), StateT, evalStateT)

import           Data.Proxy                 (Proxy (Proxy))


newtype ParserState = ParserState { identifiers :: M.Map T.Text PLC.Unique }
    deriving (Show)

data ParseError = UnknownBuiltinType T.Text
                | BuiltinTypeNotAStar T.Text
                | InvalidConstant T.Text T.Text
                deriving (Eq, Ord, Show)

instance HasErrorCode ParseError where
      errorCode UnknownBuiltinType {}  = ErrorCode 5
      errorCode BuiltinTypeNotAStar {} = ErrorCode 52
      errorCode InvalidConstant {}     = ErrorCode 4

type Error = Parsec.ParseError Char ParseError

instance ShowErrorComponent ParseError where
    showErrorComponent (UnknownBuiltinType ty) = "Unknown built-in type: " ++ T.unpack ty
    showErrorComponent (BuiltinTypeNotAStar ty) =
        "Expected a type of kind star (to later parse a constant), but got: " ++ T.unpack ty
    showErrorComponent (InvalidConstant ty con) =
        "Invalid constant: " ++ T.unpack con ++ " of type " ++ T.unpack ty

topSourcePos :: SourcePos
topSourcePos = initialPos "top"

initial :: ParserState
initial = ParserState M.empty

-- | Return the unique identifier of a name.
-- If it's not in the current parser state, map the name to a fresh id
-- and add it to the state. Used in the Name parser.
intern :: (MonadState ParserState m, PLC.MonadQuote m)
    => T.Text -> m PLC.Unique
intern n = do
    st <- get
    case M.lookup n (identifiers st) of
        Just u -> return u
        Nothing -> do
            fresh <- PLC.freshUnique
            let identifiers' = M.insert n fresh $ identifiers st
            put $ ParserState identifiers'
            return fresh

type Parser = ParsecT ParseError T.Text (StateT ParserState PLC.Quote)
instance (Stream s, PLC.MonadQuote m) => PLC.MonadQuote (ParsecT e s m)

parse :: Parser a -> String -> T.Text -> Either (ParseErrorBundle T.Text ParseError) a
parse p file str = PLC.runQuote $ parseQuoted p file str

parseQuoted :: Parser a -> String -> T.Text -> PLC.Quote (Either (ParseErrorBundle T.Text ParseError) a)
parseQuoted p file str = flip evalStateT initial $ runParserT p file str

whitespace :: Parser ()
whitespace = Lex.space space1 (Lex.skipLineComment "--") (Lex.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = Lex.lexeme whitespace

symbol :: T.Text -> Parser T.Text
symbol = Lex.symbol whitespace

lparen :: Parser T.Text
lparen = symbol "("
rparen :: Parser T.Text
rparen = symbol ")"

lbracket :: Parser T.Text
lbracket = symbol "["
rbracket :: Parser T.Text
rbracket = symbol "]"

lbrace :: Parser T.Text
lbrace = symbol "{"
rbrace :: Parser T.Text
rbrace = symbol "}"

inParens :: Parser a -> Parser a
inParens = between lparen rparen

inBrackets :: Parser a -> Parser a
inBrackets = between lbracket rbracket

inBraces :: Parser a -> Parser a
inBraces = between lbrace rbrace

isIdentifierChar :: Char -> Bool
isIdentifierChar c = isAlphaNum c || c == '_' || c == '\''

-- | Create a parser that matches the input word and returns its source position.
-- This is for attaching source positions to parsed terms/programs.
-- getSourcePos is not cheap, don't call it on matching of every token.
reservedWord ::
    -- | The word to match
    T.Text -> Parser SourcePos
reservedWord w = lexeme $ try $ getSourcePos <* symbol w

builtinFunction :: (Bounded fun, Enum fun, Pretty fun) => Parser fun
builtinFunction = lexeme $ choice $ map parseBuiltin [minBound .. maxBound]
    where parseBuiltin builtin = try $ string (display builtin) >> pure builtin

version :: Parser (PLC.Version SourcePos)
version = lexeme $ do
    p <- getSourcePos
    x <- Lex.decimal
    void $ char '.'
    y <- Lex.decimal
    void $ char '.'
    PLC.Version p x y <$> Lex.decimal

name :: Parser PLC.Name
name = lexeme $ try $ do
    void $ lookAhead letterChar
    str <- takeWhileP (Just "identifier") isIdentifierChar
    PLC.Name str <$> intern str

tyName :: Parser PLC.TyName
tyName = PLC.TyName <$> name

-- | Turn a parser that can succeed without consuming any input into one that fails in this case.
enforce :: Parser a -> Parser a
enforce p = do
    (input, x) <- match p
    guard . not $ T.null input
    pure x

-- | Consume a chunk of text and either stop on whitespace (and consume it) or on a \')\' (without
-- consuming it). We need this for collecting a @Text@ to pass it to 'PLC.parse' in order to
-- parse a built-in type or a constant. This is neither efficient (because of @manyTill anySingle@),
-- nor future-proof (what if some future built-in type has parens in its syntax?). A good way of
-- resolving this would be to turn 'PLC.parse' into a proper parser rather than just a function
-- from @Text@ - this will happen as SCP-2251 gets done.
-- Note that this also fails on @(con string \"yes (no)\")@ as well as @con unit ()@, so it really
-- should be fixed somehow.
-- (For @con unit ()@, @kwxm suggested replacing it with @unitval@ or @one@ or *)
closedChunk :: Parser T.Text
closedChunk = T.pack <$> manyTill anySingle end where
    end = enforce whitespace <|> void (lookAhead $ char ')')

-- | Parse a type tag by feeding the output of 'closedChunk' to 'PLC.parse'.
builtinTypeTag
    :: PLC.Parsable (PLC.SomeTypeIn (PLC.Kinded uni))
    => Parser (PLC.SomeTypeIn (PLC.Kinded uni))
builtinTypeTag = do
    uniText <- closedChunk
    case PLC.parse uniText of
        Nothing  -> customFailure $ UnknownBuiltinType uniText
        Just uni -> pure uni

-- | Parse a constant by parsing a type tag first and using the type-specific parser of constants.
-- Uses 'PLC.parse' under the hood for both types and constants.
-- @kwxm: this'll have problems with some built-in constants like strings and characters.
-- The existing parser has special cases involving complicated regular expressions
-- to deal with those (see Lexer.x), but things got more complicated recently when
-- @effectfully added built-in lists and pairs that can have other constants
-- nested inside them...We're probably still going to need special parsers
-- for things like quoted strings that can contain escape sequences.
-- @thealmarty will hopefully deal with these in SCP-2251.
constant
    :: forall uni.
       ( PLC.Parsable (PLC.SomeTypeIn (PLC.Kinded uni))
       , PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable
       )
    => Parser (PLC.Some (PLC.ValueOf uni))
constant = do
    -- We use 'match' for remembering the textual representation of the parsed type tag,
    -- so that we can show it in the error message if the constant fails to parse.
    (uniText, PLC.SomeTypeIn (PLC.Kinded uni)) <- match builtinTypeTag
    -- See Note [Decoding universes].
    case PLC.checkStar @uni uni of
        Nothing -> customFailure $ BuiltinTypeNotAStar uniText
        Just PLC.Refl -> do
            conText <- closedChunk
            case PLC.bring (Proxy @PLC.Parsable) uni $ PLC.parse conText of
                Nothing  -> customFailure $ InvalidConstant uniText conText
                Just con -> pure . PLC.Some $ PLC.ValueOf uni con

