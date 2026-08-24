{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Ual.Lexer
  ( lexModule
  , blockOpen
  , blockClose
  ) where

import Prelude

import Data.Text (Text)
import Data.Text qualified as Text
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Syntax
  ( BlockKind (..)
  , LexedModule (..)
  , RawBlock (..)
  , UalModuleName (..)
  )

blockOpen :: Text
blockOpen = "{-@"

{-| Note the spelling: at-sign, dash, closing brace. The UAL design doc writes
the closer the other way round (dash, at-sign, closing brace), which is not a
Haskell comment terminator at all, and makes the enclosing source file fail to
lex with an unterminated-comment error. -}
blockClose :: Text
blockClose = "@-}"

{-| Scan a surface-language source file for UAL blocks, its module name, and its
import list, in one pass. Bodies are not interpreted: see
'PlutusTx.Ual.Parser'. -}
lexModule :: Text -> Either UalError LexedModule
lexModule src = do
  blocks <- scan 1 src
  pure
    LexedModule
      { lexedModuleName = firstJust (moduleNameOf <$> lines')
      , lexedImports = concatMap (maybe [] pure . importOf) lines'
      , lexedBlocks = blocks
      }
  where
    lines' = Text.lines src

    firstJust :: [Maybe a] -> Maybe a
    firstJust xs = case [a | Just a <- xs] of
      a : _ -> Just a
      [] -> Nothing

    -- Walk the source looking for `{-@`, tracking the current line number.
    scan :: Int -> Text -> Either UalError [RawBlock]
    scan line rest =
      let (before, atOpen) = Text.breakOn blockOpen rest
          line' = line + Text.count "\n" before
       in if Text.null atOpen
            then Right []
            else
              let afterOpen = Text.drop (Text.length blockOpen) atOpen
                  (body, atClose) = Text.breakOn blockClose afterOpen
               in if Text.null atClose
                    then Left (UnterminatedBlock line')
                    else do
                      kind <- kindOf line' body
                      let bodyAfterKeyword = dropKeyword body
                          after = Text.drop (Text.length blockClose) atClose
                          nextLine = line' + Text.count "\n" body
                      rest' <- scan nextLine after
                      pure (RawBlock kind bodyAfterKeyword line' : rest')

    -- The keyword is the first whitespace-delimited word of the block.
    keywordOf :: Text -> Text
    keywordOf = Text.takeWhile (not . isSpaceChar) . Text.dropWhile isSpaceChar

    -- Everything after the keyword, verbatim. Leading whitespace before the
    -- keyword is dropped; nothing else is touched.
    dropKeyword :: Text -> Text
    dropKeyword body =
      let stripped = Text.dropWhile isSpaceChar body
       in Text.drop (Text.length (keywordOf body)) stripped

    kindOf :: Int -> Text -> Either UalError BlockKind
    kindOf line body = case keywordOf body of
      "ONCHAIN" -> Right KOnchain
      "PREDICATE" -> Right KPredicate
      "PROPERTY" -> Right KProperty
      "UPLC_DATA" -> Right KUplcData
      other -> Left (UnknownBlockKind line other)

    isSpaceChar :: Char -> Bool
    isSpaceChar c = c == ' ' || c == '\t' || c == '\n' || c == '\r'

-- | @module Foo.Bar where@ -> @Foo.Bar@. Only matches at column 0.
moduleNameOf :: Text -> Maybe UalModuleName
moduleNameOf l = case Text.words l of
  "module" : name : _ -> Just (UalModuleName (Text.dropWhileEnd (== '(') name))
  _ -> Nothing

{-| @import [qualified] Foo.Bar [as Q] [(…)]@ -> @Foo.Bar@. Only matches at
column 0, which is where Haskell import declarations live. -}
importOf :: Text -> Maybe UalModuleName
importOf l = case Text.words l of
  "import" : "qualified" : name : _ -> Just (UalModuleName (clean name))
  "import" : name : _ -> Just (UalModuleName (clean name))
  _ -> Nothing
  where
    clean = Text.takeWhile (\c -> c /= '(' && c /= ',')
