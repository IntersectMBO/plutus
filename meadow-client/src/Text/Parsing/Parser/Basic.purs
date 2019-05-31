module Text.Parsing.Parser.Basic where

import Prelude

import Control.Alternative ((<|>))
import Data.Array ((:), many)
import Data.String.CodeUnits (fromCharArray)
import Text.Parsing.Parser (ParserT)
import Text.Parsing.Parser.Combinators (between)
import Text.Parsing.Parser.String (char)
import Text.Parsing.Parser.Token (digit)

integral :: forall m. Monad m => ParserT String m String
integral = do
  firstChar <- digit <|> char '-'
  digits <- many digit
  pure $ fromCharArray (firstChar : digits)

parens :: forall m a. Monad m => ParserT String m a -> ParserT String m a
parens = between (char '(') (char ')')