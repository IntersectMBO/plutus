module Ual.Spec (tests) where

import Test.Tasty (TestTree, testGroup)
import Ual.Assurance.Spec qualified
import Ual.Blueprint.Spec qualified
import Ual.Error.Spec qualified
import Ual.Lexer.Spec qualified
import Ual.Parser.Spec qualified
import Ual.Resolve.Spec qualified

tests :: TestTree
tests =
  testGroup
    "UAL"
    [ Ual.Assurance.Spec.tests
    , Ual.Blueprint.Spec.tests
    , Ual.Error.Spec.tests
    , Ual.Lexer.Spec.tests
    , Ual.Parser.Spec.tests
    , Ual.Resolve.Spec.tests
    ]
