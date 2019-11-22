{-# LANGUAGE NamedFieldPuns      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Playground.InterpreterSpec
    ( tests
    ) where

import           Control.Monad.Except         (runExceptT)
import qualified Data.Aeson                   as JSON
import qualified Data.Aeson.Text              as JSON
import           Data.Text                    (Text)
import qualified Data.Text                    as Text
import qualified Data.Text.Lazy               as TL
import           Language.Haskell.Interpreter (SourceCode (SourceCode))
import qualified Ledger.Ada                   as Ada
import           Playground.Interpreter       (mkExpr, mkRunScript)
import           Playground.Types             (ContractCall (AddBlocks), Evaluation (Evaluation), PlaygroundError,
                                               SimulatorAction, SimulatorWallet (SimulatorWallet), program, sourceCode,
                                               wallets)
import           Test.Tasty                   (TestTree, testGroup)
import           Test.Tasty.HUnit             (assertEqual, testCase)
import           Wallet.Emulator.Types        (Wallet (Wallet))

tests :: TestTree
tests = testGroup "Playground.Interpreter" [mkRunScriptTest]

mkRunScriptTest :: TestTree
mkRunScriptTest =
    testGroup
        "mkRunScript"
        [ testCase "Should match a simple template" $ do
              let program =
                      JSON.toJSON
                          ([AddBlocks 2, AddBlocks 4] :: [SimulatorAction])
                  wallets =
                      [ SimulatorWallet (Wallet 1) (Ada.toValue 5)
                      , SimulatorWallet (Wallet 2) (Ada.toValue 10)
                      ]
              expr :: Either PlaygroundError String <-
                  runExceptT $
                  mkExpr
                      (Evaluation {sourceCode = sourceCode1, wallets, program})
              assertEqual
                  ""
                  (Right $
                   Text.stripEnd $
                   Text.unlines
                       [ "module Main where"
                       , ""
                       , "foo :: Int"
                       , "foo = 5"
                       , ""
                       , ""
                       , "main :: IO ()"
                       , "main = printJson $ stage endpoints " <>
                         toJSONString program <>
                         " " <>
                         toJSONString wallets
                       ])
                  (mkRunScript sourceCode1 . Text.pack <$> expr)
        ]

sourceCode1 :: SourceCode
sourceCode1 =
    SourceCode $ Text.unlines ["module Game where", "", "foo :: Int", "foo = 5"]

toJSONString :: JSON.ToJSON a => a -> Text
toJSONString =
    TL.toStrict .
    JSON.encodeToLazyText . JSON.String . TL.toStrict . JSON.encodeToLazyText
