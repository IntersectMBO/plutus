-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

module UntypedPlutusCore.Parser
    ( parse
    , term
    , program
    , parseTerm
    , parseTerm'
    , parseProgram
    , parseScoped
    , spanToPos
    , Parser
    , SourcePos
    ) where

import Prelude hiding (fail)

import Control.Monad.Except (MonadError, (<=<))

import PlutusCore qualified as PLC
import PlutusCore.Annotation
import PlutusPrelude (through)
import Text.Megaparsec hiding (ParseError, State, parse)
import UntypedPlutusCore.Check.Uniques (checkProgram)
import UntypedPlutusCore.Core.Type qualified as UPLC
import UntypedPlutusCore.Rename (Rename (rename))

import Data.Text (Text)
import PlutusCore.Error (AsParserErrorBundle)
import PlutusCore.MkPlc (mkIterApp)
import PlutusCore.Parser hiding (parseProgram, parseTerm, program)

-- Parsers for UPLC terms

-- | A parsable UPLC term.
type PTerm = UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun SrcSpan

conTerm :: Parser PTerm
conTerm =
    withSpan
        (\sp (_, c) -> UPLC.Constant sp c)
        (inParens' $ (,) <$> symbol "con" <*> constant)

builtinTerm :: Parser PTerm
builtinTerm =
    withSpan
        (\sp (_, fn) -> UPLC.Builtin sp fn)
        (inParens' $ (,) <$> symbol "builtin" <*> builtinFunction)

varTerm :: Parser PTerm
varTerm = withSpan UPLC.Var name'

lamTerm :: Parser PTerm
lamTerm =
    withSpan
        (\sp (_, n, body) -> UPLC.LamAbs sp n body)
        (inParens' $ (,,) <$> symbol "lam" <*> name <*> term)

appTerm :: Parser PTerm
appTerm =
    withSpan
        (\sp (fun, args) -> mkIterApp sp fun args)
        (inBrackets' $ (,) <$> term <*> some term)

delayTerm :: Parser PTerm
delayTerm =
    withSpan
        (\sp (_, body) -> UPLC.Delay sp body)
        (inParens' $ (,) <$> symbol "delay" <*> term)

forceTerm :: Parser PTerm
forceTerm =
    withSpan
        (\sp (_, body) -> UPLC.Force sp body)
        (inParens' $ (,) <$> symbol "force" <*> term)

errorTerm :: Parser PTerm
errorTerm = withSpan (const . UPLC.Error) (inParens' $ symbol "error")

-- | Parser for all UPLC terms.
term :: Parser PTerm
term = do
    whitespace
    choice $ map try [
        conTerm
        , builtinTerm
        , varTerm
        , lamTerm
        , appTerm
        , delayTerm
        , forceTerm
        , errorTerm
        ]

-- | Parser for UPLC programs.
program :: Parser (UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
program =
    whitespace >>
        withSpan
            (\sp (_, ver, body) -> UPLC.Program sp (toSpan ver) body)
            ( do
                prog <- inParens' $ (,,) <$> symbol "program" <*> version' <*> term
                notFollowedBy anySingle
                pure prog
            )
    where
        toSpan :: (UPLC.Version SourcePos, SourcePos) -> UPLC.Version SrcSpan
        toSpan (UPLC.Version start x y z, end) = UPLC.Version (toSrcSpan start end) x y z

-- | Parse a UPLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm :: (AsParserErrorBundle e, MonadError e m, PLC.MonadQuote m) => Text -> m PTerm
parseTerm = parseGen term

-- TODO: Temporary - remove once TPLC and PIR parsers are migrated to SrcSpan
parseTerm' ::
    (AsParserErrorBundle e, MonadError e m, PLC.MonadQuote m) =>
    Text ->
    m (UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun SourcePos)
parseTerm' = fmap (fmap spanToPos) . parseTerm

-- TODO: Temporary - remove once TPLC and PIR parsers are migrated to SrcSpan
spanToPos :: SrcSpan -> SourcePos
spanToPos sp = SourcePos
    { sourceName = srcSpanFile sp
    , sourceLine = mkPos $ srcSpanSLine sp
    , sourceColumn = mkPos $ srcSpanSCol sp
    }

-- | Parse a UPLC program. The resulting program will have fresh names. The
-- underlying monad must be capable of handling any parse errors.  This passes
-- "test" to the parser as the name of the input stream; to supply a name
-- explicity, use `parse program <name> <input>`.`
parseProgram ::
    (AsParserErrorBundle e, MonadError e m, PLC.MonadQuote m)
    => Text
    -> m (UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
parseProgram = parseGen program

-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
parseScoped ::
    (AsParserErrorBundle e, PLC.AsUniqueError e SrcSpan, MonadError e m, PLC.MonadQuote m)
    => Text
    -> m (UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
-- don't require there to be no free variables at this point, we might be parsing an open term
parseScoped = through (checkProgram (const True)) <=< rename <=< parseProgram
