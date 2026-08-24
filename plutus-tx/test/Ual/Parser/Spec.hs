{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Ual.Parser.Spec (tests) where

import Prelude

import Data.Text qualified as Text
import PlutusTx.Blueprint.PlutusVersion (PlutusVersion (..))
import PlutusTx.Ual.Error (UalError (..))
import PlutusTx.Ual.Parser (parseBlock)
import PlutusTx.Ual.Syntax
  ( ArgumentEncoding (..)
  , BlockKind (..)
  , ExecutionBudget (..)
  , OnchainDecl (..)
  , RawBlock (..)
  , UalArgument (..)
  , UalBlock (..)
  )
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))

tests :: TestTree
tests = testGroup "Parser" [onchainTests]

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
    , testCase "budget missing exMem" $
        onchain " [exCPU: 1] f :: A -> () "
          @?= Left (MalformedBlock 7 "budget needs both exCPU and exMem")
    ]

asOnchain :: UalBlock -> Maybe OnchainDecl
asOnchain = \case
  BOnchain d -> Just d
  _ -> Nothing
