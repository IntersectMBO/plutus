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
    ) where

import PlutusCore.Constant.Typed
import PlutusCore.Core
import PlutusCore.Core.Type
import PlutusCore.Default
import PlutusCore.Error
import PlutusCore.Mark
import PlutusCore.MkPlc (mkConstant, mkTyBuiltin)
import PlutusCore.Name
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
import PlutusCore.Parser.ParserCommon (Parser, pType, parse)
import Text.Megaparsec (SourcePos, runParserT')
import Text.Megaparsec.Error (ParseErrorBundle)

tyInst :: a -> Term tyname name uni fun a -> NonEmpty (Type tyname uni a) -> Term tyname name uni fun a
tyInst loc t (ty :| [])  = TyInst loc t ty
tyInst loc t (ty :| tys) = TyInst loc (tyInst loc t (ty:|init tys)) (last tys)

tyApps :: a -> Type tyname uni a -> NonEmpty (Type tyname uni a) -> Type tyname uni a
tyApps loc ty (ty' :| [])  = TyApp loc ty ty'
tyApps loc ty (ty' :| tys) = TyApp loc (tyApps loc ty (ty':|init tys)) (last tys)

app :: a -> Term tyname name uni fun a -> NonEmpty (Term tyname name uni fun a) -> Term tyname name uni fun a
app loc t (t' :| []) = Apply loc t t'
app loc t (t' :| ts) = Apply loc (app loc t (t':|init ts)) (last ts)

-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram ::
    String -> T.Text ->
        Either (ParseErrorBundle T.Text ParseError) (Program TyName Name DefaultUni DefaultFun SourcePos)
parseProgram = parse pProgram

-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm ::
    String -> T.Text ->
        Either (ParseErrorBundle T.Text ParseError) (Term TyName Name DefaultUni DefaultFun SourcePos)
parseTerm = parse pTerm

-- | Parse a PLC type. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseType ::
    String -> T.Text ->
        Either (ParseErrorBundle T.Text ParseError) (Type TyName DefaultUni SourcePos)
parseType = parse pType
