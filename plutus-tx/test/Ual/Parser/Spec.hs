{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Ual.Parser.Spec (tests) where

import Prelude

import Data.Text qualified as Text
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Parser (moduleUalFromSource, parseBlock)
import PlutusTx.Ual.Syntax
  ( ArgumentEncoding (..)
  , BlockKind (..)
  , ExecutionBudget (..)
  , ModuleUal (..)
  , OnchainDecl (..)
  , PropertyDecl (..)
  , RawBlock (..)
  , UalArgument (..)
  , UalBlock (..)
  , UalModuleName (..)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

tests :: TestTree
tests = testGroup "Parser" [onchainTests, otherKindTests, assemblyTests]

onchain :: Text.Text -> Either UalError UalBlock
onchain body = parseBlock (MkRawBlock KOnchain body 7)

onchainTests :: TestTree
onchainTests =
  testGroup
    "ONCHAIN"
    [ testCase "bare signature, no options, asData by default" $
        onchain " f :: Integer -> Bool "
          @?= Right
            ( BOnchain
                MkOnchainDecl
                  { onchainName = "f"
                  , onchainArgs = [MkUalArgument "Integer" AsData]
                  , onchainResult = "Bool"
                  , onchainVersion = Nothing
                  , onchainBudget = Nothing
                  , onchainLine = 7
                  , onchainResolvedArgs = []
                  }
            )
    , testCase "braced encodings, both schemes" $
        (fmap onchainArgs . asOnchain)
          <$> onchain " f :: { A : asData } -> { B : asScott } -> () "
          @?= Right (Just [MkUalArgument "A" AsData, MkUalArgument "B" AsScott])
    , testCase "mixed braced and bare arguments" $
        (fmap onchainArgs . asOnchain) <$> onchain " f :: A -> { B : asScott } -> () "
          @?= Right (Just [MkUalArgument "A" AsData, MkUalArgument "B" AsScott])
    , testCase "single colon form is also accepted" $
        (fmap onchainName . asOnchain) <$> onchain " f : A -> () "
          @?= Right (Just "f")
    , testCase "version option" $
        (fmap onchainVersion . asOnchain) <$> onchain " [version: PlutusV3] f :: A -> () "
          @?= Right (Just (Just PlutusV3))
    , testCase "budget option, both fields" $
        (fmap onchainBudget . asOnchain)
          <$> onchain " [exCPU: 1883313, exMem: 12342] f :: A -> () "
          @?= Right (Just (Just (MkExecutionBudget 1883313 12342)))
    , testCase "both options, either order" $
        (fmap onchainVersion . asOnchain)
          <$> onchain " [exCPU: 1, exMem: 2] [version: PlutusV2] f :: A -> () "
          @?= Right (Just (Just PlutusV2))
    , testCase "multi-line signature" $
        (fmap onchainArgs . asOnchain)
          <$> onchain
            ( Text.unlines
                [ " [version: PlutusV3]"
                , "    mintingContract :: { CurrencySymbol : asData }"
                , "                    -> { ScriptContext  : asData }"
                , "                    -> ()"
                ]
            )
          @?= Right
            ( Just
                [ MkUalArgument "CurrencySymbol" AsData
                , MkUalArgument "ScriptContext" AsData
                ]
            )
    , testCase "nullary function is an error, there is nothing to apply" $
        onchain " f :: () " @?= Left (MalformedBlock 7 "signature has no arguments")
    , testCase "missing signature separator" $
        onchain " f A -> () " @?= Left (MalformedBlock 7 "expected '::' or ':' after the name")
    , testCase "a colon inside a brace group is not the signature separator" $
        onchain " f A -> { B : asData } -> () "
          @?= Left (MalformedBlock 7 "expected '::' or ':' after the name")
    , testCase "unknown encoding scheme" $
        onchain " f :: { A : asBytes } -> () "
          @?= Left (MalformedBlock 7 "unknown encoding 'asBytes'; expected asData or asScott")
    , testCase "unknown plutus version" $
        onchain " [version: PlutusV9] f :: A -> () "
          @?= Left (MalformedBlock 7 "unknown version 'PlutusV9'")
    , testCase "step budget, the provisional alternative" $
        (fmap onchainBudget . asOnchain) <$> onchain " [steps: 2500] f :: A -> () "
          @?= Right (Just (Just (MkStepBudget 2500)))
    , testCase "a budget cannot be given both ways" $
        onchain " [exCPU: 1, exMem: 2, steps: 3] f :: A -> () "
          @?= Left (MalformedBlock 7 "give either exCPU and exMem, or steps, not both")
    , testCase "budget missing exMem" $
        onchain " [exCPU: 1] f :: A -> () "
          @?= Left (MalformedBlock 7 "budget needs both exCPU and exMem")
    ]

asOnchain :: UalBlock -> Maybe OnchainDecl
asOnchain = \case
  BOnchain d -> Just d
  _ -> Nothing

otherKindTests :: TestTree
otherKindTests =
  testGroup
    "other kinds"
    [ testCase "PREDICATE body passes through verbatim" $
        parseBlock (MkRawBlock KPredicate "\ndef p (x : Int) : Prop := x > 0\n" 3)
          @?= Right (BPredicate "\ndef p (x : Int) : Prop := x > 0\n")
    , testCase "UPLC_DATA takes a single type name" $
        parseBlock (MkRawBlock KUplcData "  SellDatum  " 4) @?= Right (BUplcData "SellDatum")
    , testCase "UPLC_DATA rejects two names" $
        parseBlock (MkRawBlock KUplcData " A B " 4)
          @?= Left (MalformedBlock 4 "expected exactly one type name")
    , testCase "PROPERTY: name, quoted text, body after the colon" $
        parseBlock
          ( MkRawBlock
              KProperty
              " p_one\n  \"Funds cannot be locked.\"\n : \8704 x, x \8594 x\n"
              9
          )
          @?= Right
            ( BProperty
                MkPropertyDecl
                  { propertyName = "p_one"
                  , propertyText = "Funds cannot be locked."
                  , propertyBody = "\8704 x, x \8594 x"
                  , propertyLine = 9
                  }
            )
    , testCase "PROPERTY body keeps internal newlines and indentation" $
        (fmap propertyBody . asProperty)
          <$> parseBlock (MkRawBlock KProperty " p \"t\" : a \8594\n    b\n" 1)
          @?= Right (Just "a \8594\n    b")
    , testCase "PROPERTY without text is rejected" $
        parseBlock (MkRawBlock KProperty " p : True " 1)
          @?= Left (MalformedBlock 1 "expected a quoted natural-language statement after the name")
    , testCase "PROPERTY without a body separator is rejected" $
        parseBlock (MkRawBlock KProperty " p \"t\" " 1)
          @?= Left (MalformedBlock 1 "expected ':' before the formal statement")
    , testCase "PROPERTY name may contain an underscore" $
        (fmap propertyName . asProperty)
          <$> parseBlock (MkRawBlock KProperty " p_one \"t\" : True " 1)
          @?= Right (Just "p_one")
    , testCase "PROPERTY with no name is rejected" $
        parseBlock (MkRawBlock KProperty " \"t\" : True " 1)
          @?= Left (MalformedBlock 1 "property name is empty")
    , testCase "PROPERTY name outside the assurance id pattern is rejected" $
        parseBlock (MkRawBlock KProperty " p q \"t\" : True " 1)
          @?= Left (MalformedBlock 1 "property name 'p q' must match [A-Za-z0-9_-]+")
    ]

asProperty :: UalBlock -> Maybe PropertyDecl
asProperty = \case
  BProperty d -> Just d
  _ -> Nothing

assemblyTests :: TestTree
assemblyTests =
  testGroup
    "moduleUalFromSource"
    [ testCase "collects every kind, predicates in source order" $
        moduleUalFromSource (UalModuleName "Fallback") source
          @?= Right
            MkModuleUal
              { ualModuleName = UalModuleName "My.Contract"
              , ualModuleImports = [UalModuleName "My.Types"]
              , ualOnchain =
                  [ MkOnchainDecl
                      { onchainName = "v"
                      , onchainArgs = [MkUalArgument "A" AsData]
                      , onchainResult = "()"
                      , onchainVersion = Nothing
                      , onchainBudget = Nothing
                      , onchainLine = 4
                      , onchainResolvedArgs = []
                      }
                  ]
              , ualPredicates = ["\ndef first : Prop := True\n", "\ndef second : Prop := True\n"]
              , ualProperties =
                  [ MkPropertyDecl
                      { propertyName = "p"
                      , propertyText = "t"
                      , propertyBody = "True"
                      , propertyLine = 11
                      }
                  ]
              , ualUplcData = ["D"]
              }
    , testCase "falls back to the supplied name when there is no module header" $
        (ualModuleName <$> moduleUalFromSource (UalModuleName "Fallback") "{-@ UPLC_DATA D @-}\n")
          @?= Right (UalModuleName "Fallback")
    , testCase "propagates a lexer error" $
        moduleUalFromSource (UalModuleName "M") "{-@ ONCHAIN x -@}\n"
          @?= Left (UnterminatedBlock 1)
    ]
  where
    source =
      Text.unlines
        [ "module My.Contract where" --       1
        , "import My.Types" --                2
        , "" --                               3
        , "{-@ ONCHAIN v :: A -> () @-}" --   4
        , "{-@ PREDICATE" --                  5
        , "def first : Prop := True" --       6
        , "@-}" --                            7
        , "{-@ PREDICATE" --                  8
        , "def second : Prop := True" --      9
        , "@-}" --                           10
        , "{-@ PROPERTY p \"t\" : True @-}" -- 11
        , "{-@ UPLC_DATA D @-}" --           12
        ]
