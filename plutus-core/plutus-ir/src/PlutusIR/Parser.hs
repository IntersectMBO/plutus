{-# LANGUAGE OverloadedStrings #-}

-- | Parsers for PIR terms in DefaultUni.

module PlutusIR.Parser
    ( parse
    , program
    , pType
    , pTerm
    , parseProgram
    , Parser
    , SourcePos
    ) where

import PlutusCore.Annotation
import PlutusCore.Default qualified as PLC (DefaultFun, DefaultUni)
import PlutusCore.Parser hiding (parseProgram, program)
import PlutusIR as PIR
import PlutusIR.MkPir qualified as PIR
import PlutusPrelude
import Prelude hiding (fail)

import Control.Monad.Combinators.NonEmpty qualified as NE
import Control.Monad.Except (MonadError)
import Data.Text (Text)
import PlutusCore (MonadQuote)
import PlutusCore.Error (AsParserErrorBundle)
import Text.Megaparsec hiding (ParseError, State, many, parse, some)

-- | A parsable PIR pTerm.
type PTerm = PIR.Term TyName Name PLC.DefaultUni PLC.DefaultFun SrcSpan

recursivity :: Parser Recursivity
recursivity = inParensSpc $ (symbol "rec" $> Rec) <|> (symbol "nonrec" $> NonRec)

strictness :: Parser Strictness
strictness = inParensSpc $ (symbol "strict" $> Strict) <|> (symbol "nonstrict" $> NonStrict)

varDecl :: Parser (VarDecl TyName Name PLC.DefaultUni SrcSpan)
varDecl = withSpan $ \sp ->
    inParens $ VarDecl sp <$> (symbol "vardecl" *> name) <*> pType

tyVarDecl :: Parser (TyVarDecl TyName SrcSpan)
tyVarDecl = withSpan $ \sp ->
    inParens $ TyVarDecl sp <$> (symbol "tyvardecl" *> tyName) <*> kind

datatype :: Parser (Datatype TyName Name PLC.DefaultUni SrcSpan)
datatype = withSpan $ \sp ->
    inParens $
        Datatype sp
            <$> (symbol "datatype" *> tyVarDecl)
            <*> many tyVarDecl
            <*> name
            <*> many varDecl

binding :: Parser (Binding TyName Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
binding = withSpan $ \sp ->
    inParens . choice $ try <$>
    [ TermBind sp <$> (symbol "termbind" *> strictness) <*> varDecl <*> pTerm
    , TypeBind sp <$> (symbol "typebind" *> tyVarDecl) <*> pType
    , DatatypeBind sp <$> (symbol "datatypebind" *> datatype)
    ]

varTerm :: Parser PTerm
varTerm = withSpan $ \sp ->
    PIR.Var sp <$> name'

-- A small type wrapper for parsers that are parametric in the type of term they parse
type Parametric
    = Parser PTerm -> Parser PTerm

absTerm :: Parametric
absTerm tm = withSpan $ \sp ->
    inParens $ PIR.tyAbs sp <$> (symbol "abs" *> tyName) <*> kind <*> tm

lamTerm :: Parametric
lamTerm tm = withSpan $ \sp ->
    inParens $ PIR.lamAbs sp <$> (symbol "lam" *> name) <*> pType <*> tm

conTerm :: Parametric
conTerm _tm = withSpan $ \sp ->
    inParens $ PIR.constant sp <$> (symbol "con" *> constant)

iwrapTerm :: Parametric
iwrapTerm tm = withSpan $ \sp ->
    inParens $ PIR.iWrap sp <$> (symbol "iwrap" *> pType) <*> pType <*> tm

builtinTerm :: Parametric
builtinTerm _tm = withSpan $ \sp ->
    inParens $ PIR.builtin sp <$> (symbol "builtin" *> builtinFunction)

unwrapTerm :: Parametric
unwrapTerm tm = withSpan $ \sp ->
    inParens $ PIR.unwrap sp <$> (symbol "unwrap" *> tm)

errorTerm :: Parametric
errorTerm _tm = withSpan $ \sp ->
    inParens $ PIR.error sp <$> (symbol "error" *> pType)

letTerm :: Parser PTerm
letTerm = withSpan $ \sp ->
    inParens $ Let sp <$> (symbol "let" *> recursivity) <*> NE.some (try binding) <*> pTerm

appTerm :: Parametric
appTerm tm = withSpan $ \sp ->
    inBrackets $ PIR.mkIterApp sp <$> tm <*> some tm

tyInstTerm :: Parametric
tyInstTerm tm = withSpan $ \sp ->
    inBraces $ PIR.mkIterInst sp <$> tm <*> some pType

pTerm :: Parser PTerm
pTerm = whitespace >> go
  where
    go = choice $ try <$>
        [ varTerm
        , letTerm
        , absTerm go
        , lamTerm go
        , conTerm go
        , iwrapTerm go
        , builtinTerm go
        , unwrapTerm go
        , errorTerm go
        , tyInstTerm go
        , appTerm go
        ]

-- Note that PIR programs do not actually carry a version number
-- we (optionally) parse it all the same so we can parse all PLC code
program :: Parser (Program TyName Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
program = do
    whitespace
    prog <- withSpan $ \sp ->
        inParens $ Program sp <$> (symbol "program" *> option () (void version) *> pTerm)
    notFollowedBy anySingle
    pure prog

-- | Parse a PIR program. The resulting program will have fresh names. The
-- underlying monad must be capable of handling any parse errors.  This passes
-- "test" to the parser as the name of the input stream; to supply a name
-- explicity, use `parse program <name> <input>`.
parseProgram ::
    (AsParserErrorBundle e, MonadError e m, MonadQuote m)
    => Text
    -> m (Program TyName Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
parseProgram = parseGen program
