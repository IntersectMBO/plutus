{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module TransformSpec (transform) where

import Common
import PlcTestUtils
import TestLib

import PlutusCore.Quote

import PlutusCore qualified as PLC
import PlutusCore.Pretty qualified as PLC

import PlutusIR.Analysis.RetainedSize qualified as RetainedSize
import PlutusIR.Parser
import PlutusIR.Transform.Beta qualified as Beta
import PlutusIR.Transform.DeadCode qualified as DeadCode
import PlutusIR.Transform.Inline qualified as Inline
import PlutusIR.Transform.LetFloat qualified as LetFloat
import PlutusIR.Transform.LetMerge qualified as LetMerge
import PlutusIR.Transform.NonStrict qualified as NonStrict
import PlutusIR.Transform.RecSplit qualified as RecSplit
import PlutusIR.Transform.Rename ()
import PlutusIR.Transform.ThunkRecursions qualified as ThunkRec
import PlutusIR.Transform.Unwrap qualified as Unwrap

import Control.Monad
import PlutusIR.Error as PIR
import PlutusIR.TypeCheck as TC
import Text.Megaparsec.Pos


transform :: TestNested
transform = testNested "transform" [
    thunkRecursions
    , nonStrict
    , letFloat
    , recSplit
    , inline
    , beta
    , unwrapCancel
    , deadCode
    , retainedSize
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
    $ map (goldenPirM goldenFloatTC term)
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
  ,"nonrec9"
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
  ,"oldFloatBug"
  ,"outRhs"
  ,"outLam"
  ,"inLam"
  ,"rhsSqueezeVsNest"
  ]
 where
   goldenFloatTC pir = rethrow . asIfThrown @(PIR.Error PLC.DefaultUni PLC.DefaultFun ()) $ do
       let pirFloated = RecSplit.recSplit . LetFloat.floatTerm . runQuote $ PLC.rename pir
       -- make sure the floated result typechecks
       _ <- runQuoteT . flip inferType (() <$ pirFloated) =<< TC.getDefTypeCheckConfig ()
       -- letmerge is not necessary for floating, but is a nice visual transformation
       pure $ LetMerge.letMerge pirFloated

recSplit :: TestNested
recSplit =
    testNested "recSplit"
    $ map (goldenPir (RecSplit.recSplit . runQuote . PLC.rename) $ term @PLC.DefaultUni @PLC.DefaultFun)
  [
    "truenonrec"
  , "mutuallyRecursiveTypes"
  , "mutuallyRecursiveValues"
  , "selfrecursive"
  , "small"
  , "big"
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
    , "single"
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
    , "pruneDatatype"
    ]

retainedSize :: TestNested
retainedSize =
    testNested "retainedSize"
    $ map (goldenPir renameAndAnnotate $ term @PLC.DefaultUni @PLC.DefaultFun)
    [ "typeLet"
    , "termLet"
    , "strictLet"
    , "nonstrictLet"
    -- @Maybe@ is referenced, so it retains all of the data type.
    , "datatypeLiveType"
    -- @Nothing@ is referenced, so it retains all of the data type.
    , "datatypeLiveConstr"
    -- @match_Maybe@ is referenced, so it retains all of the data type.
    , "datatypeLiveDestr"
    , "datatypeDead"
    , "singleBinding"
    , "builtinBinding"
    , "etaBuiltinBinding"
    , "etaBuiltinBindingUsed"
    , "nestedBindings"
    , "nestedBindingsIndirect"
    , "recBindingSimple"
    , "recBindingComplex"
    ] where
        displayAnnsConfig = PLC.PrettyConfigClassic PLC.defPrettyConfigName True
        renameAndAnnotate
            = PLC.AttachPrettyConfig displayAnnsConfig
            . RetainedSize.annotateWithRetainedSize
            . runQuote
            . PLC.rename

rename :: TestNested
rename =
    testNested "rename"
    $ map (goldenPir (PLC.AttachPrettyConfig debugConfig . runQuote . PLC.rename) $ term @PLC.DefaultUni @PLC.DefaultFun)
    [ "allShadowedDataNonRec"
    , "allShadowedDataRec"
    , "paramShadowedDataNonRec"
    , "paramShadowedDataRec"
    ] where
        debugConfig = PLC.PrettyConfigClassic PLC.debugPrettyConfigName False
