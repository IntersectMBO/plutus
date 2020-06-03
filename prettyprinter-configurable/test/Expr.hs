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

data Expr
    = Var Text                   -- ^ A variable.
    | Not Expr                   -- ^ Boolean NOT.
    | Or Expr Expr               -- ^ Boolean OR.
    | And Expr Expr              -- ^ Boolean AND.
    | Eq Expr Expr               -- ^ Integer equality.
    | Neg Expr                   -- ^ Integer negation (unary minus).
    | Add Expr Expr              -- ^ Addition.
    | Mul Expr Expr              -- ^ Multiplication.
    | Fac Expr                   -- ^ Factorial.
    | IfThenElse Expr Expr Expr  -- ^ @if_then_else_@
    deriving (Show)

-- Prefix and right-associative, so that @~(~b)@ is pretty-printed as @~~b@.
notFixity :: Fixity
notFixity = Fixity RightAssociative 9

orFixity :: Fixity
orFixity = Fixity RightAssociative 2

andFixity :: Fixity
andFixity = Fixity RightAssociative 3

eqFixity :: Fixity
eqFixity = Fixity NonAssociative 4

-- Prefix and left-associative, so that @- (- x)@ is pretty-printed as @- (- x)@.
-- Has the same associativity as @+@, so that @(- x) + y@ is pretty-printed as @- x + y@.
negFixity :: Fixity
negFixity = Fixity LeftAssociative 6

addFixity :: Fixity
addFixity = Fixity LeftAssociative 6

mulFixity :: Fixity
mulFixity = Fixity LeftAssociative 7

-- Postfix and left-associative, so that @(x!)!@ is pretty-printed as @x!!@.
facFixity :: Fixity
facFixity = Fixity LeftAssociative 9

ifThenElseFixity :: Fixity
ifThenElseFixity = Fixity RightAssociative (-5)

instance PrettyBy RenderContext Expr where
    prettyBy = inContextM $ \case
        Var v -> unitDocM $ pretty v
        Not e ->
            sequenceDocM ToTheRight notFixity $ \prettyEl ->
                "~" <> prettyEl e
        Or e1 e2 ->
            infixDocM orFixity $ \prettyL prettyR ->
                prettyL e1 <+> "||" <+> prettyR e2
        And e1 e2 ->
            infixDocM andFixity $ \prettyL prettyR ->
                prettyL e1 <+> "&&" <+> prettyR e2
        Eq e1 e2 ->
            infixDocM eqFixity $ \prettyL prettyR ->
                prettyL e1 <+> "==" <+> prettyR e2
        Neg e ->
            sequenceDocM ToTheRight negFixity $ \prettyEl ->
                "-" <+> prettyEl e
        Add e1 e2 ->
            infixDocM addFixity $ \prettyL prettyR ->
                prettyL e1 <+> "+" <+> prettyR e2
        Mul e1 e2 ->
            infixDocM mulFixity $ \prettyL prettyR ->
                prettyL e1 <+> "*" <+> prettyR e2
        Fac e ->
            sequenceDocM ToTheLeft facFixity $ \prettyEl ->
                prettyEl e <> "!"
        IfThenElse c e1 e2 ->
            infixDocM ifThenElseFixity $ \prettyL prettyR ->
                group . hang 4 $ vsep
                    [ "if"   <+> prettyL c
                    , "then" <+> prettyR e1
                    , "else" <+> prettyR e2
                    ]

-- #############################################
-- ## A quick parser for tests to be readable ##
-- #############################################

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
    [ [ operator Prefix "~" Not
      , operator Postfix "!" Fac
      ]
    , [ operator InfixL "*" Mul
      ]
    , [ operator InfixL "+" Add
      , operator Prefix "-" Neg
      ]
    , [ operator InfixN "==" Eq
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

-- ###########
-- ## Tests ##
-- ###########

makeTestCase :: Expr -> String -> TestTree
makeTestCase expr res = testCase res $ show (prettyBy botRenderContext expr) @?= res

test_expr :: TestTree
test_expr = testGroup "expr"
    [ makeTestCase "(a)" "a"

    , makeTestCase "(~(a))" "~a"
    , makeTestCase "~(~a)" "~~a"
    , makeTestCase "~(a || b)" "~(a || b)"
    , makeTestCase "~(a && b)" "~(a && b)"
    , makeTestCase "((~a) || (~b))" "~a || ~b"
    , makeTestCase "((~a) && (~b))" "~a && ~b"

    , makeTestCase "((a) && (b))" "a && b"
    , makeTestCase "(a && b) && c" "(a && b) && c"
    , makeTestCase "a && (b && c)" "a && b && c"
    , makeTestCase "(a && b) || (c && d)" "a && b || c && d"
    , makeTestCase "(a || b) && (c || d)" "(a || b) && (c || d)"

    , makeTestCase "-(a)" "- a"
    , makeTestCase "-(-a)" "- (- a)"
    , makeTestCase "-(a + b)" "- (a + b)"
    , makeTestCase "-(a * b)" "- a * b"
    , makeTestCase "(-a) + (-b)" "- a + (- b)"
    , makeTestCase "(-a) * (-b)" "(- a) * (- b)"

    , makeTestCase "(a)!" "a!"
    , makeTestCase "(a!)!" "a!!"
    , makeTestCase "(a + b)!" "(a + b)!"
    , makeTestCase "(a * b)!" "(a * b)!"
    , makeTestCase "(a!) + (b!)" "a! + b!"
    , makeTestCase "(a!) * (b!)" "a! * b!"

    , makeTestCase "-(a!)" "- a!"
    , makeTestCase "(-a)!" "(- a)!"

    , makeTestCase "((a) + (b))" "a + b"
    , makeTestCase "(a + b) + c" "a + b + c"
    , makeTestCase "a + (b + c)" "a + (b + c)"
    , makeTestCase "(a * b) + (c * d)" "a * b + c * d"
    , makeTestCase "(a + b) * (c + d)" "(a + b) * (c + d)"
    , makeTestCase "(a + b) == (c * d)" "a + b == c * d"

    , makeTestCase "if (a) then (b) else (c)" "if a then b else c"
    , makeTestCase
          "if if a then b else c then if d then e else f else if g then h else i"
          "if (if a then b else c) then if d then e else f else if g then h else i"

    , makeTestCase "~(if a then b else c)" "~(if a then b else c)"
    , makeTestCase "-(if a then b else c)" "- (if a then b else c)"
    , makeTestCase "(if a then b else c)!" "(if a then b else c)!"

    , makeTestCase "if (a && b) then (c || d) else (e == f)" "if a && b then c || d else e == f"
    , makeTestCase "a || (if b then c else d)" "a || (if b then c else d)"
    , makeTestCase "(if a then b else c) && d" "(if a then b else c) && d"

    , makeTestCase "if (a == b) then (c + d) else (e * f)" "if a == b then c + d else e * f"
    , makeTestCase "a + (if b then c else d)" "a + (if b then c else d)"
    , makeTestCase "(if a then b else c) * d" "(if a then b else c) * d"

    , makeTestCase "(a + if b then c else d) * e" "(a + (if b then c else d)) * e"
    , makeTestCase "(a * if b then c else d) * e" "a * (if b then c else d) * e"
    ]
