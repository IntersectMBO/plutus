{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}


module PlutusCore.Parser
    ( parseProgram
    , parseTerm
    , parseType
    , ParseError(..)
    ) where

import Data.ByteString.Lazy (ByteString)
import Data.Text qualified as T
import PlutusCore.Core (Program (..), Term (..), Type)
import PlutusCore.Default
import PlutusCore.Error (ParseError (..))
import PlutusCore.Name (Name, TyName)
import PlutusCore.Parser.ParserCommon
import Text.Megaparsec (MonadParsec (notFollowedBy), SourcePos, anySingle, choice, getSourcePos, try)
import Text.Megaparsec.Error (ParseErrorBundle)

-- Parsers for PLC terms

-- | A parsable PLC term.
type PTerm = Term TyName Name DefaultUni DefaultFun SourcePos

varTerm :: Parser PTerm
varTerm = Var <$> getSourcePos <*> name

tyAbsTerm :: Parser PTerm
tyAbsTerm = inParens $ TyAbs <$> wordPos "abs" <*> tyName  <*> kind <*> term

lamTerm :: Parser PTerm
lamTerm = inParens $ LamAbs <$> wordPos "lam" <*> name <*> pType <*> term

appTerm :: Parser PTerm
appTerm = inBrackets $ do
    pos <- getSourcePos
    tm <- term
    tms <- appTerms
    pure $ app pos tm tms

app :: SourcePos -> PTerm -> [PTerm] -> PTerm
app _  _t []        = error "appTerm, app: An application without an argument."
app loc t [t']      = Apply loc t t'
app loc t (t' : ts) = Apply loc (app loc t (t':init ts)) (last ts)

-- | The syntax allows @(app (app x y) z)@ to be written as [x y z]
-- rather than [[x y] z]. This deals with more than one application.
appTerms :: Parser [PTerm]
appTerms = choice
    [ try terms
    , do
        tm <- term
        pure [tm]
    ]
    where terms = do
            tm <- term
            tms <- appTerms
            pure $ tm : tms

conTerm :: Parser PTerm
conTerm = inParens $ Constant <$> wordPos "con" <*> constant

builtinTerm :: Parser PTerm
builtinTerm = inParens $ Builtin <$> wordPos "builtin" <*> builtinFunction

tyInstTerm :: Parser PTerm
tyInstTerm = inBraces $ do
    pos <- getSourcePos
    tm <- term
    tys <- appTypes
    pure $ tyInst pos tm tys

appTypes :: Parser [PType]
appTypes = choice
    [ try types
    , do
        ty <- pType
        pure [ty]
    ]
    where types = do
            ty <- pType
            tys <- appTypes
            pure $ ty : tys

tyInst :: SourcePos -> PTerm -> [PType] -> PTerm
tyInst _  _t []         = error "tyInst: A type instantiation without an argument."
tyInst loc t [ty]       = TyInst loc t ty
tyInst loc t (ty : tys) = TyInst loc (tyInst loc t (ty : init tys)) (last tys)

unwrapTerm :: Parser PTerm
unwrapTerm = inParens $ Unwrap <$> wordPos "unwrap" <*> term

iwrapTerm :: Parser PTerm
iwrapTerm = inParens $ IWrap <$> wordPos "iwrap" <*> pType <*> pType <*> term

errorTerm
    :: Parser PTerm
errorTerm = inParens $ Error <$> wordPos "error" <*> pType

-- | Parser for all PLC terms.
term :: Parser PTerm
term = choice $ map try
    [ tyAbsTerm
    , lamTerm
    , appTerm
    , conTerm
    , builtinTerm
    , tyInstTerm
    , unwrapTerm
    , iwrapTerm
    , errorTerm
    , varTerm
    ]

-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram ::
    ByteString -> Either (ParseErrorBundle T.Text ParseError) (Program TyName Name DefaultUni DefaultFun SourcePos)
parseProgram = parseGen program

-- | Parser for PLC programs.
program :: Parser (Program TyName Name DefaultUni DefaultFun SourcePos)
program = whitespace >> do
    prog <- inParens $ Program <$> wordPos "program" <*> version <*> term
    notFollowedBy anySingle
    return prog

-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm ::
    ByteString ->
        Either (ParseErrorBundle T.Text ParseError) (Term TyName Name DefaultUni DefaultFun SourcePos)
parseTerm = parseGen term

-- | Parse a PLC type. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseType ::
    ByteString ->
        Either (ParseErrorBundle T.Text ParseError) (Type TyName DefaultUni SourcePos)
parseType = parseGen pType
