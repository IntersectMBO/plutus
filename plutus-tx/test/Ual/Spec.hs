module Ual.Spec (tests) where

import Test.Tasty (TestTree, testGroup)
import Ual.Error.Spec qualified
import Ual.Lexer.Spec qualified

tests :: TestTree
tests = testGroup "UAL" [Ual.Error.Spec.tests, Ual.Lexer.Spec.tests]
