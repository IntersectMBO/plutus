{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module TransformSpec (transform) where

import           Common
import           TestLib

import           PlutusCore.Quote

import qualified PlutusCore                         as PLC
import qualified PlutusCore.Pretty                  as PLC

import           PlutusIR.Parser
import qualified PlutusIR.Transform.Beta            as Beta
import qualified PlutusIR.Transform.DeadCode        as DeadCode
import qualified PlutusIR.Transform.Inline          as Inline
import qualified PlutusIR.Transform.LetFloat        as LetFloat
import qualified PlutusIR.Transform.LetMerge        as LetMerge
import qualified PlutusIR.Transform.NonStrict       as NonStrict
import           PlutusIR.Transform.Rename          ()
import qualified PlutusIR.Transform.ThunkRecursions as ThunkRec
import qualified PlutusIR.Transform.Unwrap          as Unwrap

import           Control.Monad
import           Text.Megaparsec.Pos

transform :: TestNested
transform = testNested "transform" [
    thunkRecursions
    , nonStrict
    , letFloat
    , inline
    , beta
    , unwrapCancel
    , deadCode
    , rename
    ]

thunkRecursions :: TestNested
thunkRecursions = testNested "thunkRecursions"
    $ map (goldenPir ThunkRec.thunkRecursions $ term @PLC.DefaultUni @PLC.DefaultFun)
    [ "listFold"
    , "monoMap"
    ]

nonStrict :: TestNested
nonStrict = testNested "nonStrict"
    $ map (goldenPir (runQuote . NonStrict.compileNonStrictBindings False) $ term @PLC.DefaultUni @PLC.DefaultFun)
    [ "nonStrict1"
    ]

letFloat :: TestNested
letFloat =
    testNested "letFloat"
    $ map (goldenPir (LetMerge.letMerge . LetFloat.floatTerm . runQuote . PLC.rename) $ term @PLC.DefaultUni @PLC.DefaultFun)
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
  ,"strictNonValueDeep"
  ,"regression1"
  ]

instance Semigroup SourcePos where
  p1 <> _ = p1

instance Monoid SourcePos where
  mempty = initialPos ""

inline :: TestNested
inline =
    testNested "inline"
    $ map (goldenPir (runQuote . (Inline.inline <=< PLC.rename)) $ term @PLC.DefaultUni @PLC.DefaultFun)
    [ "var"
    , "builtin"
    , "constant"
    , "transitive"
    , "tyvar"
    ]


beta :: TestNested
beta =
    testNested "beta"
    $ map (goldenPir (Beta.beta . runQuote . PLC.rename) $ term @PLC.DefaultUni @PLC.DefaultFun)
    [ "lamapp"
    , "absapp"
    ]

unwrapCancel :: TestNested
unwrapCancel =
    testNested "unwrapCancel"
    $ map (goldenPir Unwrap.unwrapCancel $ term @PLC.DefaultUni @PLC.DefaultFun)
    -- Note: these examples don't typecheck, but we don't care
    [ "unwrapWrap"
    , "wrapUnwrap"
    ]

deadCode :: TestNested
deadCode =
    testNested "deadCode"
    $ map (goldenPir (runQuote . DeadCode.removeDeadBindings) $ term @PLC.DefaultUni @PLC.DefaultFun)
    [ "typeLet"
    , "termLet"
    , "strictLet"
    , "nonstrictLet"
    , "datatypeLiveType"
    , "datatypeLiveConstr"
    , "datatypeLiveDestr"
    , "datatypeDead"
    , "singleBinding"
    , "builtinBinding"
    , "etaBuiltinBinding"
    , "nestedBindings"
    , "nestedBindingsIndirect"
    , "recBindingSimple"
    , "recBindingComplex"
    ]

rename :: TestNested
rename =
    testNested "rename"
    $ map (goldenPir (PLC.AttachPrettyConfig debugConfig . runQuote . PLC.rename) $ term @PLC.DefaultUni @PLC.DefaultFun)
    [ "allShadowedDataNonRec"
    , "allShadowedDataRec"
    , "paramShadowedDataNonRec"
    , "paramShadowedDataRec"
    ] where
        debugConfig = PLC.PrettyConfigClassic PLC.debugPrettyConfigName
