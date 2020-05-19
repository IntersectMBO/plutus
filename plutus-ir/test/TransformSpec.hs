{-# LANGUAGE OverloadedStrings #-}
module TransformSpec where

import           Common
import           TestLib

import           Language.PlutusCore.Quote

import qualified Language.PlutusCore                         as PLC
import           Language.PlutusIR.Parser
import qualified Language.PlutusIR.Transform.LetFloat        as LetFloat
import qualified Language.PlutusIR.Transform.NonStrict       as NonStrict
import           Language.PlutusIR.Transform.Rename          ()
import qualified Language.PlutusIR.Transform.ThunkRecursions as ThunkRec
import           Text.Megaparsec.Pos

transform :: TestNested
transform = testNested "transform" [
    thunkRecursions
    , nonStrict
    , letFloat
    ]

thunkRecursions :: TestNested
thunkRecursions = testNested "thunkRecursions"
    $ map (goldenPir ThunkRec.thunkRecursions term)
    [ "listFold"
    , "monoMap"
    ]

nonStrict :: TestNested
nonStrict = testNested "nonStrict"
    $ map (goldenPir (runQuote . NonStrict.compileNonStrictBindings) term)
    [ "nonStrict1"
    ]

letFloat :: TestNested

letFloat = testNested "letFloat"
    $ map (goldenPir (LetFloat.floatTerm . runQuote . PLC.rename) term)
  [ "letInLet"
  ,"listMatch"
  ,"maybe"
  ,"ifError"
  ,"mutuallyRecursiveTypes"
  ,"mutuallyRecursiveValues"
  ,"nonrec1"
  ,"nonrec2"
  ,"nonrec3"
  ,"nonrec4"
  ,"nonrec6"
  ,"nonrec7"
  ,"nonrec8"
  ,"rec1"
  ,"rec2"
  ,"rec3"
  ,"rec4"
  ,"nonrecToRec"
  ,"nonrecToNonrec"
  ,"oldLength"
  ,"strictValue"
  ,"strictNonValue"
  ,"strictNonValue2"
  ,"strictNonValue3"
  ,"strictValueNonValue"
  ,"strictValueValue"
  ,"even3Eval"
  ]

instance Semigroup SourcePos where
  p1 <> p2 = p1

instance Monoid SourcePos where
  mempty = initialPos ""
