module Test.Main where

import Prelude
import JsonEncodingTests as JsonEncodingTests
import ChainTests as ChainTests
import CursorTests as CursorTests
import Data.Array.ExtraTests as Data.Array.ExtraTests
import Data.Foldable.ExtraTests as Data.Foldable.ExtraTests
import Data.String.ExtraTests as Data.String.ExtraTests
import EditorTests as EditorTests
import Effect (Effect)
import GistsTests as GistsTests
import StaticDataTests as StaticDataTests
import PlutusTx.AssocMapTests as PlutusTx.AssocMapTests
import MainFrameTests as MainFrameTests
import Test.Unit.Main (runTest)
import Schema.TypesTests as Schema.TypesTests

foreign import forDeps :: Effect Unit

main :: Effect Unit
main =
  runTest do
    JsonEncodingTests.all
    ChainTests.all
    CursorTests.all
    Data.Array.ExtraTests.all
    Data.Foldable.ExtraTests.all
    Data.String.ExtraTests.all
    EditorTests.all
    GistsTests.all
    StaticDataTests.all
    PlutusTx.AssocMapTests.all
    MainFrameTests.all
    Schema.TypesTests.all
