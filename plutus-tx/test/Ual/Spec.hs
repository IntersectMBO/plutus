module Ual.Spec (tests) where

import Test.Tasty (TestTree, testGroup)
import Ual.Lexer.Spec qualified

tests :: TestTree
tests = testGroup "UAL" [Ual.Lexer.Spec.tests]
