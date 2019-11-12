module Text.Parsing.Parser.Basic where

import Prelude hiding (between)
import Control.Alternative ((<|>))
import Data.Array (foldl, many, mapWithIndex, (:))
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (drop, fromCharArray, take)
import Data.String.CodeUnits as String
import Text.Parsing.Parser (ParserT)
import Text.Parsing.Parser.Combinators (between)
import Text.Parsing.Parser.Pos (Position(..))
import Text.Parsing.Parser.String (char)
import Text.Parsing.Parser.Token (digit)

integral :: forall m. Monad m => ParserT String m String
integral = do
  firstChar <- digit <|> char '-'
  digits <- many digit
  pure $ fromCharArray (firstChar : digits)

parens :: forall m a. Monad m => ParserT String m a -> ParserT String m a
parens = between (char '(') (char ')')

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

replaceInPosition :: Position -> Position -> String -> String -> String
replaceInPosition (Position start) (Position end) value initial =
  unlines
    $ mapWithIndex
        ( \i line ->
            if i == (start.line - 1) then
              (take (start.column - 1) line) <> value <> (drop (end.column - 1) line)
            else
              line
        )
    $ lines initial
