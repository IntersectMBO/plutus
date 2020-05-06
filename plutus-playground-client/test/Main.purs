module Test.Main where

import Prelude
import JsonEncodingTests as JsonEncodingTests
import ChainTests as ChainTests
import CursorTests as CursorTests
import Data.Array.ExtraTests as Data.Array.ExtraTests
import Data.String.ExtraTests as Data.String.ExtraTests
import EditorTests as EditorTests
import Effect (Effect)
import GistsTests as GistsTests
import StaticDataTests as StaticDataTests
import Language.PlutusTx.AssocMapTests as Language.PlutusTx.AssocMapTests
import MainFrameTests as MainFrameTests
import Test.Unit.Main (runTest)
import TypesTests as TypesTests

foreign import forDeps :: Effect Unit

main :: Effect Unit
main =
  runTest do
    JsonEncodingTests.all
    ChainTests.all
    CursorTests.all
    Data.Array.ExtraTests.all
    Data.String.ExtraTests.all
    EditorTests.all
    GistsTests.all
    StaticDataTests.all
    Language.PlutusTx.AssocMapTests.all
    MainFrameTests.all
    TypesTests.all
