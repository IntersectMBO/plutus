module Text.Parsing.StringParser.Basic where

import Prelude hiding (between)
import Control.Alternative ((<|>))
import Data.Array (foldl, many, some, (:))
import Data.Array as Array
import Data.Bifunctor (bimap)
import Data.Either (Either)
import Data.Foldable (foldMap)
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (drop, fromCharArray, singleton, take)
import Data.String.CodeUnits as String
import Text.Parsing.StringParser (ParseError, Parser(..), Pos)
import Text.Parsing.StringParser.CodeUnits (anyDigit, char, string, satisfy, skipSpaces)
import Text.Parsing.StringParser.Combinators (between, option)

integral :: Parser String
integral = do
  sign <- option "" (string "-")
  firstChar <- anyDigit
  digits <- many (many (char '_') *> anyDigit)
  pure $ sign <> fromCharArray (firstChar : digits)

parens :: forall a. Parser a -> Parser a
parens p =
  between (char '(') (char ')') do
    skipSpaces
    res <- p
    skipSpaces
    pure res

whiteSpaceChar :: Parser Char
whiteSpaceChar = satisfy \c -> c == '\n' || c == '\r' || c == ' ' || c == '\t'

-- | Match some whitespace characters.
someWhiteSpace :: Parser String
someWhiteSpace = do
  cs <- some whiteSpaceChar
  pure (foldMap singleton cs)

unlines :: Array String -> String
unlines = foldl f ""
  where
  f :: String -> String -> String
  f acc a = acc <> a <> "\n"

lines :: String -> Array String
lines = map String.fromCharArray <<< go <<< String.toCharArray
  where
  go :: Array Char -> Array (Array Char)
  go s = case Array.uncons s of
    Nothing -> []
    Just _ ->
      let
        withBreaks = break ((==) '\n') s
      in
        withBreaks.init `Array.cons` go (stripNewLine withBreaks.rest)

  stripNewLine :: Array Char -> Array Char
  stripNewLine s = case Array.uncons s of
    Nothing -> []
    Just { head: '\n', tail: tail } -> tail
    Just { head: head, tail: tail } -> head `Array.cons` tail

  -- | `break p as` is `span (not <<< p) as`.
  break :: forall a. (a -> Boolean) -> Array a -> { init :: (Array a), rest :: (Array a) }
  break p = Array.span (not <<< p)

replaceInPosition :: { start :: Pos, end :: Pos, string :: String, replacement :: String } -> String
replaceInPosition { start, end, string, replacement } = take start string <> replacement <> drop end string

runParser' :: forall a. Parser a -> String -> Either { error :: ParseError, pos :: Pos } a
runParser' (Parser p) s = bimap identity _.result (p { str: s, pos: 0 })
