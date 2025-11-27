{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}

module Unicode.Spec where

import Control.Lens (view)
import Data.Text (Text)
import PlutusCore.MkPlc (mkConstant)
import PlutusTx (CompiledCode, compile, getPlcNoAnn, liftCodeDef)
import PlutusTx.Builtins (BuiltinString)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit (testCase, (@?=))
import UntypedPlutusCore (progTerm)

tests :: TestTree
tests =
  testGroup
    "Unicode"
    [ testCase "Unicode characters are supported" do
        let
          code :: CompiledCode BuiltinString
          code = $$(compile [||"λ"||])

          lifted :: CompiledCode BuiltinString
          lifted = liftCodeDef "λ"

          term = view progTerm . getPlcNoAnn

        term code @?= term lifted
        term code @?= mkConstant () ("λ" :: Text)
    ]
