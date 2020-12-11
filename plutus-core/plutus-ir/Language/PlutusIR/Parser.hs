{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.PlutusIR.Parser
    ( topSourcePos
    , parse
    , parseQuoted
    , term
    , typ
    , program
    , plcTerm
    , plcProgram
    , Parser
    , ParseError (..)
    , Error
    , SourcePos
    ) where

import           Prelude                            hiding (fail)

import           Control.Applicative                hiding (many, some)
import           Control.Monad.State                hiding (fail)

import qualified Language.PlutusCore                as PLC
import qualified Language.PlutusCore.Parsable       as PLC
import           Language.PlutusIR                  as PIR
import qualified Language.PlutusIR.MkPir            as PIR
import           PlutusPrelude                      (Pretty, display)
import           Text.Megaparsec                    hiding (ParseError, State, parse)
import qualified Text.Megaparsec                    as Parsec

import           Data.Char
import           Data.Foldable
import qualified Data.Map                           as M
import           Data.Proxy
import qualified Data.Text                          as T

import qualified Control.Monad.Combinators.NonEmpty as NE
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer         as Lex




newtype ParserState = ParserState { identifiers :: M.Map T.Text PLC.Unique }
    deriving (Show)

data ParseError = UnknownBuiltinType T.Text
                | InvalidConstant T.Text T.Text
                deriving (Eq, Ord, Show)

type Error = Parsec.ParseError Char ParseError

instance ShowErrorComponent ParseError where
    showErrorComponent (UnknownBuiltinType ty) = "Unknown built-in type: " ++ T.unpack ty
    showErrorComponent (InvalidConstant ty con) =
        "Invalid constant: " ++ T.unpack con ++ " of type " ++ T.unpack ty

topSourcePos :: SourcePos
topSourcePos = initialPos "top"

initial :: ParserState
initial = ParserState M.empty

intern :: (MonadState ParserState m, PLC.MonadQuote m) => T.Text -> m PLC.Unique
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

-- Tokens
-- TODO: move this to separate module?

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

reservedWord :: T.Text -> Parser SourcePos
reservedWord w = lexeme $ try $ do
    p <- getSourcePos
    void $ string w
    notFollowedBy (satisfy isIdentifierChar)
    return p

builtinFunction :: (Bounded fun, Enum fun, Pretty fun) => Parser fun
builtinFunction = lexeme $ choice $ map parseBuiltin [minBound .. maxBound]
    where parseBuiltin builtin = try $ string (display builtin) >> pure builtin

name :: Parser Name
name = lexeme $ try $ do
    void $ lookAhead letterChar
    str <- takeWhileP (Just "identifier") isIdentifierChar
    Name str <$> intern str

var :: Parser Name
var = name

tyVar :: Parser TyName
tyVar = TyName <$> name

version :: Parser (PLC.Version SourcePos)
version = lexeme $ do
    p <- getSourcePos
    x <- Lex.decimal
    void $ char '.'
    y <- Lex.decimal
    void $ char '.'
    PLC.Version p x y <$> Lex.decimal

recursivity :: Parser Recursivity
recursivity = inParens $ (reservedWord "rec" >> return Rec) <|> (reservedWord "nonrec" >> return NonRec)

strictness :: Parser Strictness
strictness = inParens $ (reservedWord "strict" >> return Strict) <|> (reservedWord "nonstrict" >> return NonStrict)

funType
    :: PLC.Parsable (PLC.Some uni)
    => Parser (Type TyName uni SourcePos)
funType = TyFun <$> reservedWord "fun" <*> typ <*> typ

allType
    :: PLC.Parsable (PLC.Some uni)
    => Parser (Type TyName uni SourcePos)
allType = TyForall <$> reservedWord "all" <*> tyVar <*> kind <*> typ

lamType
    :: PLC.Parsable (PLC.Some uni)
    => Parser (Type TyName uni SourcePos)
lamType = TyLam <$> reservedWord "lam" <*> tyVar <*> kind <*> typ

ifixType
    :: PLC.Parsable (PLC.Some uni)
    => Parser (Type TyName uni SourcePos)
ifixType = TyIFix <$> reservedWord "ifix" <*> typ <*> typ

conType
    :: PLC.Parsable (PLC.Some uni)
    => Parser (Type TyName uni SourcePos)
conType = reservedWord "con" >> builtinType

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
-- from @Text@, but PLC's parser also uses 'PLC.parse' and it's currently not @megaparsec@-based,
-- and so mixing two distinct parsing machines doesn't sound too exciting.
--
-- Note that this also fails on @(con string \"yes (no)\")@ as well as @con unit ()@, so it really
-- should be fixed somehow.
closedChunk :: Parser T.Text
closedChunk = T.pack <$> manyTill anySingle end where
    end = enforce whitespace <|> void (lookAhead $ char ')')

-- | Parse a type tag by feeding the output of 'closedChunk' to 'PLC.parse'.
builtinTypeTag
    :: PLC.Parsable (PLC.Some uni)
    => Parser (PLC.Some uni)
builtinTypeTag = do
    uniText <- closedChunk
    case PLC.parse uniText of
        Nothing  -> customFailure $ UnknownBuiltinType uniText
        Just uni -> pure uni

-- | Parse a constant by parsing a type tag first and using the type-specific parser of constants.
-- Uses 'PLC.parse' under the hood for both types and constants.
constant
    :: (PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable)
    => Parser (PLC.Some (PLC.ValueOf uni))
constant = do
    -- We use 'match' for remembering the textual representation of the parsed type tag,
    -- so that we can show it in the error message if the constant fails to parse.
    (uniText, PLC.Some uni) <- match builtinTypeTag
    conText <- closedChunk
    case PLC.bring (Proxy @PLC.Parsable) uni $ PLC.parse conText of
        Nothing  -> customFailure $ InvalidConstant uniText conText
        Just con -> pure . PLC.Some $ PLC.ValueOf uni con

builtinType
    :: PLC.Parsable (PLC.Some uni)
    => Parser (Type TyName uni SourcePos)
builtinType = do
    p <- getSourcePos
    PLC.Some uni <- builtinTypeTag
    pure . TyBuiltin p . PLC.Some $ PLC.TypeIn uni

appType
    :: PLC.Parsable (PLC.Some uni)
    => Parser (Type TyName uni SourcePos)
appType = do
    pos  <- getSourcePos
    fn   <- typ
    args <- some typ
    pure $ foldl' (TyApp pos) fn args

kind :: Parser (Kind SourcePos)
kind = inParens (typeKind <|> funKind)
    where
        typeKind = Type <$> reservedWord "type"
        funKind  = KindArrow <$> reservedWord "fun" <*> kind <*> kind

typ
    :: PLC.Parsable (PLC.Some uni)
    => Parser (Type TyName uni SourcePos)
typ = (tyVar >>= (\n -> getSourcePos >>= \p -> return $ TyVar p n))
    <|> (inParens $ funType <|> allType <|> lamType <|> ifixType <|> conType)
    <|> inBrackets appType

varDecl
    :: PLC.Parsable (PLC.Some uni)
    => Parser (VarDecl TyName Name uni fun SourcePos)
varDecl = inParens $ VarDecl <$> reservedWord "vardecl" <*> var <*> typ

tyVarDecl :: Parser (TyVarDecl TyName SourcePos)
tyVarDecl = inParens $ TyVarDecl <$> reservedWord "tyvardecl" <*> tyVar <*> kind

datatype
    :: PLC.Parsable (PLC.Some uni)
    => Parser (Datatype TyName Name uni fun SourcePos)
datatype = inParens $ Datatype <$> reservedWord "datatype"
    <*> tyVarDecl
    <*> many tyVarDecl
    <*> var
    <*> many varDecl

binding
    :: ( PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable
       , Bounded fun, Enum fun, Pretty fun
       )
    => Parser (Binding TyName Name uni fun SourcePos)
binding = inParens $
    (try $ reservedWord "termbind" >> TermBind <$> getSourcePos <*> strictness <*> varDecl <*> term)
    <|> (reservedWord "typebind" >> TypeBind <$> getSourcePos <*> tyVarDecl <*> typ)
    <|> (reservedWord "datatypebind" >> DatatypeBind <$> getSourcePos <*> datatype)

-- A small type wrapper for parsers that are parametric in the type of term they parse
type Parametric uni fun
    = forall term. PIR.TermLike term TyName Name uni fun
    => Parser (term SourcePos)
    -> Parser (term SourcePos)

absTerm :: Parametric uni fun
absTerm tm = PIR.tyAbs <$> reservedWord "abs" <*> tyVar <*> kind <*> tm

lamTerm :: PLC.Parsable (PLC.Some uni) => Parametric uni fun
lamTerm tm = PIR.lamAbs <$> reservedWord "lam" <*> name <*> typ <*> tm

conTerm
    :: (PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable)
    => Parametric uni fun
conTerm _tm = PIR.constant <$> reservedWord "con" <*> constant

iwrapTerm :: PLC.Parsable (PLC.Some uni) => Parametric uni fun
iwrapTerm tm = PIR.iWrap <$> reservedWord "iwrap" <*> typ <*> typ <*> tm

builtinTerm :: (Bounded fun, Enum fun, Pretty fun) => Parametric uni fun
builtinTerm _term = PIR.builtin <$> reservedWord "builtin" <*> builtinFunction

unwrapTerm :: Parametric uni fun
unwrapTerm tm = PIR.unwrap <$> reservedWord "unwrap" <*> tm

errorTerm :: PLC.Parsable (PLC.Some uni) => Parametric uni fun
errorTerm _tm = PIR.error <$> reservedWord "error" <*> typ

letTerm
    :: ( PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable
       , Bounded fun, Enum fun, Pretty fun
       )
    => Parser (Term TyName Name uni fun SourcePos)
letTerm = Let <$> reservedWord "let" <*> recursivity <*> NE.some (try binding) <*> term

appTerm :: Parametric uni fun
appTerm tm = PIR.mkIterApp <$> getSourcePos <*> tm <*> some tm

tyInstTerm :: PLC.Parsable (PLC.Some uni) => Parametric uni fun
tyInstTerm tm = PIR.mkIterInst <$> getSourcePos <*> tm <*> some typ

term'
    :: ( PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable
       , Bounded fun, Enum fun, Pretty fun
       )
    => Parametric uni fun
term' other = (var >>= (\n -> getSourcePos >>= \p -> return $ PIR.var p n))
    <|> (inParens $ absTerm self <|> lamTerm self <|> conTerm self <|> iwrapTerm self <|> builtinTerm self <|> unwrapTerm self <|> errorTerm self <|> other)
    <|> inBraces (tyInstTerm self)
    <|> inBrackets (appTerm self)
    where self = term' other

term
    :: ( PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable
       , Bounded fun, Enum fun, Pretty fun
       )
    => Parser (Term TyName Name uni fun SourcePos)
term = term' letTerm

plcTerm
    :: ( PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable
       , Bounded fun, Enum fun, Pretty fun
       )
    => Parser (PLC.Term TyName Name uni fun SourcePos)
plcTerm = term' empty

-- Note that PIR programs do not actually carry a version number
-- we (optionally) parse it all the same so we can parse all PLC code
program
    :: ( PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable
       , Bounded fun, Enum fun, Pretty fun
       )
    => Parser (Program TyName Name uni fun SourcePos)
program = whitespace >> do
    prog <- inParens $ do
        p <- reservedWord "program"
        option () $ void version
        Program p <$> term
    notFollowedBy anySingle
    return prog

plcProgram
    :: ( PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable
       , Bounded fun, Enum fun, Pretty fun
       )
    => Parser (PLC.Program TyName Name uni fun SourcePos)
plcProgram = whitespace >> do
    prog <- inParens $ PLC.Program <$> reservedWord "program" <*> version <*> plcTerm
    notFollowedBy anySingle
    return prog
