{-# LANGUAGE OverloadedStrings #-}

module PlutusTx.Ual.Lexer
  ( lexModule
  , blockOpen
  , blockClose
  ) where

import Prelude

import Data.Char (isSpace)
import Data.Maybe (listToMaybe, mapMaybe)
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
import list. Two traversals: one over the raw text for blocks, one over the
lines for the module header and imports.

Block bodies are not interpreted. Only the kind keyword is read; everything
after it is passed through verbatim, because the body is Lean source that only
Lean will ever parse. -}
lexModule :: Text -> Either UalError LexedModule
lexModule src = do
  blocks <- scan 1 src
  pure
    MkLexedModule
      { lexedModuleName = listToMaybe (mapMaybe moduleNameOf lines')
      , lexedImports = mapMaybe importOf lines'
      , lexedBlocks = blocks
      }
  where
    lines' = Text.lines src

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
                      -- The keyword is the first whitespace-delimited word of
                      -- the block. Everything after it is the body: leading
                      -- whitespace before the keyword is dropped, and nothing
                      -- else is touched.
                      let (keyword, bodyAfterKeyword) =
                            Text.break isSpace (Text.dropWhile isSpace body)
                      kind <- kindOf line' keyword
                      let after = Text.drop (Text.length blockClose) atClose
                          nextLine = line' + Text.count "\n" body
                      rest' <- scan nextLine after
                      pure (MkRawBlock kind bodyAfterKeyword line' : rest')

    kindOf :: Int -> Text -> Either UalError BlockKind
    kindOf line keyword = case keyword of
      "ONCHAIN" -> Right KOnchain
      "PREDICATE" -> Right KPredicate
      "PROPERTY" -> Right KProperty
      "UPLC_DATA" -> Right KUplcData
      other -> Left (UnknownBlockKind line other)

{-| Drop an export or import list that runs straight into the module name with
no intervening space, as in @module Foo.Bar(x, y) where@. -}
trimName :: Text -> Text
trimName = Text.takeWhile (\c -> c /= '(' && c /= ',')

{-| @module Foo.Bar where@ -> @Foo.Bar@. Matches at any indentation, for the
reason given on @importOf@. -}
moduleNameOf :: Text -> Maybe UalModuleName
moduleNameOf l = case Text.words l of
  "module" : name : _ -> Just (UalModuleName (trimName name))
  _ -> Nothing

{-| @import [qualified] Foo.Bar [as Q] [(…)]@ -> @Foo.Bar@.

@Text.words@ ignores leading whitespace, so this matches at any indentation,
not only at column 0 where real Haskell import declarations live. That is
deliberate: over-collecting an import is harmless, because the import graph is
later intersected with the set of modules that actually produced UAL fragments,
whereas missing one loses a real dependency edge. -}
importOf :: Text -> Maybe UalModuleName
importOf l = case Text.words l of
  "import" : "qualified" : name : _ -> Just (UalModuleName (trimName name))
  "import" : name : _ -> Just (UalModuleName (trimName name))
  _ -> Nothing
