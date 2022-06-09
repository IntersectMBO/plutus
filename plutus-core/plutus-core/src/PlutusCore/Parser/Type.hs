{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds         #-}

module PlutusCore.Parser.Type where

import PlutusPrelude

import PlutusCore.Core.Type
import PlutusCore.Default
import PlutusCore.MkPlc (mkIterTyApp)
import PlutusCore.Name
import PlutusCore.Parser.ParserCommon

import Control.Monad
import Text.Megaparsec hiding (ParseError, State, many, parse, some)

import Data.Text (Text, pack)
import PlutusCore.Error
import PlutusCore.Quote

-- | A PLC @Type@ to be parsed. ATM the parser only works
-- for types in the @DefaultUni@ with @DefaultFun@.
type PType = Type TyName DefaultUni SourcePos

varType :: Parser PType
varType = TyVar <$> getSourcePos <*> tyName

funType :: Parser PType
funType = inParens $ TyFun <$> wordPos "fun" <*> pType <*> pType

allType :: Parser PType
allType = inParens $ TyForall <$> wordPos "all" <*> tyName <*> kind <*> pType

lamType :: Parser PType
lamType = inParens $ TyLam <$> wordPos "lam" <*> tyName <*> kind <*> pType

ifixType :: Parser PType
ifixType = inParens $ TyIFix <$> wordPos "ifix" <*> pType <*> pType

builtinType :: Parser PType
builtinType = inParens $ TyBuiltin <$> wordPos "con" <*> ((\(SomeTypeIn (Kinded uni)) -> SomeTypeIn uni) <$> defaultUniType)

appType :: Parser PType
appType = inBrackets $ do
    pos  <- getSourcePos
    fn   <- pType
    args <- some pType
    pure $ mkIterTyApp pos fn args

kind :: Parser (Kind SourcePos)
kind = inParens (typeKind <|> funKind)
    where
        typeKind = Type <$> wordPos "type"
        funKind  = KindArrow <$> wordPos "fun" <*> kind <*> kind

-- | Parser for @PType@.
pType :: Parser PType
pType = choice $ map try
    [ funType
    , ifixType
    , allType
    , builtinType
    , lamType
    , appType
    , varType
    ]

defaultUniPart :: Parser (SomeTypeIn (Kinded DefaultUni))
defaultUniPart = choice $ map try
    [ inParens defaultUniType
    , SomeTypeIn (Kinded DefaultUniInteger) <$ symbol "integer"
    , SomeTypeIn (Kinded DefaultUniByteString) <$ symbol "bytestring"
    , SomeTypeIn (Kinded DefaultUniString) <$ symbol "string"
    , SomeTypeIn (Kinded DefaultUniUnit) <$ symbol "unit"
    , SomeTypeIn (Kinded DefaultUniBool) <$ symbol "bool"
    , SomeTypeIn (Kinded DefaultUniProtoList) <$ symbol "list"
    , SomeTypeIn (Kinded DefaultUniProtoPair) <$ symbol "pair"
    , SomeTypeIn (Kinded DefaultUniData) <$ symbol "data"
    ]
defaultUniType :: Parser (SomeTypeIn (Kinded DefaultUni))
defaultUniType = do
    f <- defaultUniPart
    as <- many defaultUniPart
    foldM uniApplyM f as

tyName :: Parser TyName
tyName = TyName <$> name





doIt :: forall a. Show a => Parser a -> String -> IO ()
doIt p = print . parseIt . pack where
    parseIt :: Text -> Either ParserErrorBundle a
    parseIt = runQuoteT . parseGen p

-- >>> doIt defaultUniType "list"
-- Right (SomeTypeIn (Kinded list))
-- >>> doIt defaultUniType "list integer"
-- Right (SomeTypeIn (Kinded list (integer)))
-- >>> doIt defaultUniType "pair (list bool)"
-- Right (SomeTypeIn (Kinded pair (list (bool))))
-- >>> doIt defaultUniType "pair (list unit) integer"
-- Right (SomeTypeIn (Kinded pair (list (unit)) (integer)))
-- >>> doIt defaultUniType "list (pair unit integer)"
-- Right (SomeTypeIn (Kinded list (pair (unit) (integer))))
-- >>> doIt defaultUniType "pair unit (pair bool integer)"
-- Right (SomeTypeIn (Kinded pair (unit) (pair (bool) (integer))))
