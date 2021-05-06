module Template.Format (formatText) where

import Prelude
import Data.String (codePointFromChar, drop, length, take, takeWhile)
import Halogen.HTML (HTML, b_, text)

-- We want to include some very basic formatting in the metadata. A full implementation of
-- something like Markdown would clearly be overkill (at least for now). So we just have
-- this very simple function instead that puts text surrounded by asterisks in bold.
formatText :: forall p a. String -> Array (HTML p a)
formatText "" = []

formatText string =
  if take 1 string == "*" then
    let
      boldText = takeWhile ((/=) asterisk) (drop 1 string)

      rest = drop ((length boldText) + 2) string
    in
      [ b_ [ text boldText ] ] <> formatText rest
  else
    let
      plainText = takeWhile ((/=) asterisk) string

      rest = drop (length plainText) string
    in
      [ text plainText ] <> formatText rest
  where
  asterisk = codePointFromChar '*'
