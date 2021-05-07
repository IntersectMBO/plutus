module Template.Format (formatText) where

import Prelude
import Data.String (CodePoint, codePointFromChar, drop, length, take, takeWhile)
import Halogen.HTML (HTML, b_, text)

-- We want to include some very basic formatting in the metadata. A full implementation of
-- something like Markdown would clearly be overkill (at least for now). So we just have
-- this very simple function instead that puts text surrounded by asterisks in bold.
formatText :: forall p a. String -> Array (HTML p a)
formatText "" = []

formatText string
  | take 2 string == "\\*" =
    let
      rest = drop 2 string
    in
      [ text "*" ] <> formatText rest

formatText string
  | take 1 string == "*" =
    let
      boldText = takeWhile ((/=) asterisk) (drop 1 string)

      rest = drop ((length boldText) + 2) string
    in
      [ b_ [ text boldText ] ] <> formatText rest

formatText string =
  let
    plainText = takeWhile (\c -> c /= asterisk && c /= backslash) string

    rest = drop (length plainText) string
  in
    [ text plainText ] <> formatText rest

asterisk :: CodePoint
asterisk = codePointFromChar '*'

backslash :: CodePoint
backslash = codePointFromChar '\\'
