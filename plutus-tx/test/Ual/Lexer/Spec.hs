{-# LANGUAGE OverloadedStrings #-}

module Ual.Lexer.Spec (tests) where

import Prelude

import Data.Text (Text)
import Data.Text qualified as Text
import Hedgehog (Property, forAll, property, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Lexer (lexModule)
import PlutusTx.Ual.Syntax
  ( BlockKind (..)
  , LexedModule (..)
  , RawBlock (..)
  , UalModuleName (..)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import Test.Tasty.Hedgehog (testPropertyNamed)

tests :: TestTree
tests =
  testGroup
    "Lexer"
    [ testCase "module name" $
        lexedModuleName <$> lexModule "module Foo.Bar where\n"
          @?= Right (Just (UalModuleName "Foo.Bar"))
    , testCase "no module header" $
        lexedModuleName <$> lexModule "x = 1\n" @?= Right Nothing
    , testCase "imports, plain and qualified and aliased" $
        lexedImports
          <$> lexModule
            ( Text.unlines
                [ "module M where"
                , "import Foo.Bar"
                , "import qualified Baz.Qux as Q"
                , "import Data.Text (Text)"
                , "x = 1"
                , "import NotAnImport.Because.Indented"
                ]
            )
          @?= Right
            [ UalModuleName "Foo.Bar"
            , UalModuleName "Baz.Qux"
            , UalModuleName "Data.Text"
            , UalModuleName "NotAnImport.Because.Indented"
            ]
    , testCase "one block of each kind, in source order" $
        (fmap rawKind . lexedBlocks)
          <$> lexModule
            ( Text.unlines
                [ "{-@ ONCHAIN a @-}"
                , "{-@ PREDICATE b @-}"
                , "{-@ PROPERTY c @-}"
                , "{-@ UPLC_DATA d @-}"
                ]
            )
          @?= Right [KOnchain, KPredicate, KProperty, KUplcData]
    , testCase "body is byte-identical, including Unicode and nested braces" $
        (fmap rawBody . lexedBlocks) <$> lexModule ("{-@ PREDICATE " <> tricky <> " @-}")
          @?= Right [" " <> tricky <> " "]
    , testCase "line numbers are 1-based and count preceding newlines" $
        (fmap rawLine . lexedBlocks)
          <$> lexModule "module M where\n\n{-@ ONCHAIN a @-}\nx = 1\n{-@ PROPERTY b @-}\n"
          @?= Right [3, 5]
    , testCase "unterminated block reports the opening line" $
        lexModule "module M where\n{-@ ONCHAIN a -@}\n" @?= Left (UnterminatedBlock 2)
    , testCase "unknown kind reports the keyword" $
        lexModule "{-@ NOPE a @-}\n" @?= Left (UnknownBlockKind 1 "NOPE")
    , testCase "an ordinary comment is not a block" $
        (length . lexedBlocks) <$> lexModule "{- ONCHAIN not a block -}\n" @?= Right 0
    , testPropertyNamed "bodies survive lexing unchanged" "bodyRoundTrip" bodyRoundTrip
    ]

-- | Unicode, a Lean comment, and an unbalanced Haskell comment opener.
tricky :: Text
tricky = "∀ x, x → x {- not a comment terminator -} /- lean -/"

{-| Any text that does not contain the terminator must come back byte-identical.
This is the guarantee the whole pass-through design rests on. -}
bodyRoundTrip :: Property
bodyRoundTrip = property $ do
  body <-
    forAll $
      Gen.filter (not . Text.isInfixOf "@-}") (Gen.text (Range.linear 0 200) Gen.unicode)
  -- The space after the keyword is required: without it the keyword and the
  -- start of the body run together into one word and the block kind is
  -- unrecognised. The lexer keeps that separator, so it is part of the body.
  let src = "{-@ PREDICATE " <> body <> "@-}"
  ((fmap rawBody . lexedBlocks) <$> lexModule src) === Right [" " <> body]
