{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}

module Expr
    ( test_expr
    ) where

import           Text.Pretty
import           Text.PrettyBy
import           Text.PrettyBy.Fixity

import           Control.Monad.Combinators.Expr
import           Data.Bifunctor
import           Data.Char
import           Data.Functor.Identity
import           Data.String
import           Data.Text                      (Text)
import           Data.Void
import           Test.Tasty
import           Test.Tasty.HUnit
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer     as Lexer

-- >>> True && if False then False else True
-- True
-- >>> (if False then False else True) && True
-- True

data Expr
    = Var Text
    | Not Expr
    | And Expr Expr
    | Or Expr Expr
    | Eq Expr Expr
    | IfThenElse Expr Expr Expr
    deriving (Show)

andFixity :: Fixity
andFixity = Fixity 3 RightAssociative

orFixity :: Fixity
orFixity = Fixity 2 RightAssociative

eqFixity :: Fixity
eqFixity = Fixity 4 LeftAssociative

ifThenElseFixity :: Fixity
ifThenElseFixity = Fixity (-5) NonAssociative

instance PrettyBy RenderContext Expr where
    prettyBy = inContextM $ \case
        Var v -> unitDocM $ pretty v
        Not e ->
            sequenceDocM juxtFixity $ \prettyEl ->
                "not" <+> prettyEl e
        And e1 e2 ->
            infixDocM andFixity $ \prettyL prettyR ->
                prettyL e1 <+> "&&" <+> prettyR e2
        Or e1 e2 ->
            infixDocM orFixity $ \prettyL prettyR ->
                prettyL e1 <+> "||" <+> prettyR e2
        Eq e1 e2 ->
            infixDocM eqFixity $ \prettyL prettyR ->
                prettyL e1 <+> "==" <+> prettyR e2
        IfThenElse c e1 e2 ->
            withPrettyAt Forward ifThenElseFixity $ \prettyBot ->
                encloseM ifThenElseFixity . group . hang 4 $ vsep
                    [ "if" <+> prettyBot c
                    , "then" <+> prettyBot e1
                    , "else" <+> prettyBot e2
                    ]



-- >>> prettyBy botRenderContext $ IfThenElse (Bool True) (Bool False) (And (Bool False) (Bool True))
-- if True then False else False && True

-- >>> prettyBy botRenderContext $ IfThenElse (Bool True) (And (Bool False) (And (Bool False) (And (Bool False) (And (Bool False) (And (Bool False) (Bool True)))))) (And (Bool False) (Bool True))
-- if True
--     then False && False && False && False && False && True
--     else False && True

-- >>> prettyBy botRenderContext $ And (Bool True) (IfThenElse (Bool True) (And (Bool False) (And (Bool False) (And (Bool False) (And (Bool False) (And (Bool False) (Bool True)))))) (And (Bool False) (Bool True)))
-- True && (if True
--              then False && False && False && False && False && True
--              else False && True)

-- >>> prettyBy botRenderContext $ "a" `Or` Not "b"

-- >>> prettyBy botRenderContext $ Not (Bool True) `And` Bool False
-- not true && false

-- >>> prettyBy botRenderContext $ (Bool False `And` Bool True) `Or`
-- false || not true

-- >>> prettyBy botRenderContext $ Not (Bool True) `And` Bool False
-- not true && false


whitespace :: (MonadParsec e s m, Token s ~ Char) => m ()
whitespace = Lexer.space space1 empty empty

symbol :: (MonadParsec e s m, Token s ~ Char) => Tokens s -> m (Tokens s)
symbol = Lexer.symbol whitespace

lexeme :: (MonadParsec e s m, Token s ~ Char) => m a -> m a
lexeme = Lexer.lexeme whitespace

operator
    :: (MonadParsec e s m, Token s ~ Char)
    => (m op -> Operator m expr) -> Tokens s -> op -> Operator m expr
operator fixity name op = fixity $ op <$ symbol name

type Parser = ParsecT Void Text Identity

opTable :: [[Operator Parser Expr]]
opTable =
    [ [ operator Prefix "not" Not
      ]
    , [ operator InfixL "==" Eq
      ]
    , [ operator InfixR "&&" And
      ]
    , [ operator InfixR "||" Or
      ]
    ]

isIdChar :: Char -> Bool
isIdChar = isAlphaNum

exprP :: Parser Expr
exprP = makeExprParser termP opTable

varP :: Parser Expr
varP = lexeme $ Var <$> takeWhileP Nothing isIdChar

keywordP :: Text -> Parser ()
keywordP name = lexeme $ string name *> notFollowedBy (satisfy isIdChar)

ifThenElseP :: Parser Expr
ifThenElseP =
    IfThenElse
        <$> (try $ keywordP "if" *> exprP)
        <*> (keywordP "then" *> exprP)
        <*> (keywordP "else" *> exprP)

termP :: Parser Expr
termP = choice
    [ between (symbol "(") (symbol ")") exprP
    , ifThenElseP
    , varP
    ]

parseExpr :: Text -> Either String Expr
parseExpr = first errorBundlePretty . runParser (between whitespace eof exprP) ""

instance IsString Expr where
    fromString = either error id . parseExpr . fromString

-- >>> :set -XOverloadedStrings
-- >>> "b" :: Expr
-- Var "b"
-- >>> parseExpr "if b then c else d"
-- Right (IfThenElse (Var "b") (Var "c") (Var "d"))

-- a or (not b)
-- (a and b) or c
-- (a or b) and b

makeTestCase :: Expr -> String -> TestTree
makeTestCase expr res = testCase res $ show (prettyBy botRenderContext expr) @?= res

test :: Bool
test = b where b = _

test_expr :: TestTree
test_expr = testGroup "expr"
    [ makeTestCase "(a)" "a"
    , makeTestCase "(not (a))" "not a"
    , makeTestCase "((a) && (b))" "a && b"
    , makeTestCase "((not a) || (not b))" "not a || not b"
    , makeTestCase "(a && b) || (c && d)" "a && b || c && d"
    , makeTestCase "(a || b) && (c || d)" "(a || b) && (c || d)"
    , makeTestCase "(a && b) == (c || d)" "(a && b) == (c || d)"
    , makeTestCase "(a || b) == (c && d)" "(a || b) == (c && d)"
    , makeTestCase "(a == b) || (c == d)" "a == b || c == d"
    , makeTestCase "(a && b) && c" "(a && b) && c"
    , makeTestCase "a && (b && c)" "a && b && c"
    , makeTestCase "(a == b) == c" "a == b == c"
    , makeTestCase "a == (b == c)" "a == (b == c)"
    , makeTestCase "if (a) then (b) else (c)" "if a then b else c"
    , makeTestCase "if (a && b) then (c || d) else (e == f)" "if a && b then c || d else e == f"
    , makeTestCase "a || if b then c else d" "a || (if b then c else d)"
    , makeTestCase "(if a then b else c) && d" "(if a then b else c) && d"
    , makeTestCase
          "if if a then b else c then if d then e else f else if g then h else i"
          "if (if a then b else c) then (if d then e else f) else (if g then h else i)"
    ]
