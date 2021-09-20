module EditorTests
  ( all
  ) where

import Data.Traversable (traverse_)
import Editor.Types (allKeyBindings, readKeyBindings)
import Prelude
import Test.Unit (TestSuite, suite, test)
import Test.Unit.Assert (equal)

all :: TestSuite
all =
  suite "Editor" do
    readShowKeyBindingsTests

readShowKeyBindingsTests :: TestSuite
readShowKeyBindingsTests =
  test "readShowKeyBindingsTests" do
    traverse_ (\keyBindings -> equal keyBindings (readKeyBindings (show keyBindings))) allKeyBindings
