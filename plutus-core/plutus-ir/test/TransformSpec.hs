{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module TransformSpec where

import Test.Tasty
import Test.Tasty.Extras

import PlutusCore.Quote

import PlutusCore qualified as PLC
import PlutusCore.Name
import PlutusCore.Pretty qualified as PLC
import PlutusPrelude

import Control.Monad.Except
import PlutusIR.Analysis.RetainedSize qualified as RetainedSize
import PlutusIR.Check.Uniques as Uniques
import PlutusIR.Core.Instance.Pretty.Readable
import PlutusIR.Core.Type
import PlutusIR.Error as PIR
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.Beta qualified as Beta
import PlutusIR.Transform.CommuteFnWithConst qualified as CommuteFnWithConst
import PlutusIR.Transform.DeadCode qualified as DeadCode
import PlutusIR.Transform.EvaluateBuiltins qualified as EvaluateBuiltins
import PlutusIR.Transform.Inline.Inline qualified as Inline
import PlutusIR.Transform.KnownCon qualified as KnownCon
import PlutusIR.Transform.LetFloatIn qualified as LetFloatIn
import PlutusIR.Transform.LetFloatOut qualified as LetFloatOut
import PlutusIR.Transform.LetMerge qualified as LetMerge
import PlutusIR.Transform.NonStrict qualified as NonStrict
import PlutusIR.Transform.RecSplit qualified as RecSplit
import PlutusIR.Transform.Rename ()
import PlutusIR.Transform.StrictifyBindings qualified as StrictifyBindings
import PlutusIR.Transform.Unwrap qualified as Unwrap
import PlutusIR.TypeCheck as TC

test_transform :: TestTree
test_transform = runTestNestedIn ["plutus-ir/test"] transform

transform :: TestNested
transform =
    testNested
        "transform"
        [ retainedSize
        , rename
        , commuteDefaultFun
        , strictifyBindings
        ]

instance Semigroup PLC.SrcSpan where
    sp1 <> _ = sp1

instance Monoid PLC.SrcSpan where
    mempty = initialSrcSpan ""


retainedSize :: TestNested
retainedSize =
    testNested "retainedSize" $
        map
            (goldenPir renameAndAnnotate pTerm)
            [ "typeLet"
            , "termLet"
            , "strictLet"
            , "nonstrictLet"
            , -- @Maybe@ is referenced, so it retains all of the data type.
              "datatypeLiveType"
            , -- @Nothing@ is referenced, so it retains all of the data type.
              "datatypeLiveConstr"
            , -- @match_Maybe@ is referenced, so it retains all of the data type.
              "datatypeLiveDestr"
            , "datatypeDead"
            , "singleBinding"
            , "builtinBinding"
            , "etaBuiltinBinding"
            , "etaBuiltinBindingUsed"
            , "nestedBindings"
            , "nestedBindingsIndirect"
            , "recBindingSimple"
            , "recBindingComplex"
            ]
  where
    displayAnnsConfig = PLC.PrettyConfigClassic PLC.defPrettyConfigName True
    renameAndAnnotate =
        PLC.AttachPrettyConfig displayAnnsConfig
            . RetainedSize.annotateWithRetainedSize def
            . runQuote
            . PLC.rename

rename :: TestNested
rename =
    testNested "rename" $
        map
            (goldenPir (PLC.AttachPrettyConfig debugConfig . runQuote . PLC.rename) pTerm)
            [ "allShadowedDataNonRec"
            , "allShadowedDataRec"
            , "paramShadowedDataNonRec"
            , "paramShadowedDataRec"
            ]
  where
    debugConfig = PLC.PrettyConfigClassic PLC.debugPrettyConfigName False

commuteDefaultFun :: TestNested
commuteDefaultFun =
    testNested "commuteDefaultFun" $
    map
        (goldenPir CommuteFnWithConst.commuteDefaultFun pTerm)
        [ "equalsInt" -- this tests that the function works on equalInteger
        , "divideInt" -- this tests that the function excludes not commutative functions
        , "multiplyInt" -- this tests that the function works on multiplyInteger
        , "let" -- this tests that it works in the subterms
        ]

strictifyBindings :: TestNested
strictifyBindings =
    testNested "strictifyBindings" $
        map
            (goldenPir (StrictifyBindings.strictifyBindings def) pTerm)
            [ "pure1"
            , "impure1"
            , "unused"
            , "conapp"
            ]
