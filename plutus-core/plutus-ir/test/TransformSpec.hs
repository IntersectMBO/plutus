{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module TransformSpec (transform) where

import Test.Tasty.Extras

import PlutusCore.Quote

import PlutusCore qualified as PLC
import PlutusCore.Pretty qualified as PLC
import PlutusPrelude

import PlutusIR.Analysis.RetainedSize qualified as RetainedSize
import PlutusIR.Error as PIR
import PlutusIR.Parser
import PlutusIR.Test
import PlutusIR.Transform.Beta qualified as Beta
import PlutusIR.Transform.DeadCode qualified as DeadCode
import PlutusIR.Transform.Inline.CallSiteInline (computeArity)
import PlutusIR.Transform.Inline.Inline qualified as Inline
import PlutusIR.Transform.LetFloatIn qualified as LetFloatIn
import PlutusIR.Transform.LetFloatOut qualified as LetFloatOut
import PlutusIR.Transform.LetMerge qualified as LetMerge
import PlutusIR.Transform.NonStrict qualified as NonStrict
import PlutusIR.Transform.RecSplit qualified as RecSplit
import PlutusIR.Transform.Rename ()
import PlutusIR.Transform.ThunkRecursions qualified as ThunkRec
import PlutusIR.Transform.Unwrap qualified as Unwrap
import PlutusIR.TypeCheck as TC

transform :: TestNested
transform =
    testNested
        "transform"
        [ thunkRecursions
        , nonStrict
        , letFloatOut
        , letFloatInConservative
        , letFloatInRelaxed
        , recSplit
        , inline
        , computeArityTest
        , beta
        , unwrapCancel
        , deadCode
        , retainedSize
        , rename
        ]

thunkRecursions :: TestNested
thunkRecursions =
    testNested "thunkRecursions" $
        map
            (goldenPir (ThunkRec.thunkRecursions def) pTerm)
            [ "listFold"
            , "monoMap"
            , "errorBinding"
            ]

nonStrict :: TestNested
nonStrict =
    testNested "nonStrict" $
        map
            (goldenPir (runQuote . NonStrict.compileNonStrictBindings False) pTerm)
            [ "nonStrict1"
            ]

letFloatOut :: TestNested
letFloatOut =
    testNested "letFloatOut" $
        map
            (goldenPirM goldenFloatTC pTerm)
            [ "letInLet"
            , "listMatch"
            , "maybe"
            , "ifError"
            , "mutuallyRecursiveTypes"
            , "mutuallyRecursiveValues"
            , "nonrec1"
            , "nonrec2"
            , "nonrec3"
            , "nonrec4"
            , "nonrec6"
            , "nonrec7"
            , "nonrec8"
            , "nonrec9"
            , "rec1"
            , "rec2"
            , "rec3"
            , "rec4"
            , "nonrecToRec"
            , "nonrecToNonrec"
            , "oldLength"
            , "strictValue"
            , "strictNonValue"
            , "strictNonValue2"
            , "strictNonValue3"
            , "strictValueNonValue"
            , "strictValueValue"
            , "even3Eval"
            , "strictNonValueDeep"
            , "oldFloatBug"
            , "outRhs"
            , "outLam"
            , "inLam"
            , "rhsSqueezeVsNest"
            ]
  where
    goldenFloatTC pir = rethrow . asIfThrown @(PIR.Error PLC.DefaultUni PLC.DefaultFun ()) $ do
        let pirFloated = RecSplit.recSplit . LetFloatOut.floatTerm def . runQuote $ PLC.rename pir
        -- make sure the floated result typechecks
        _ <- runQuoteT . flip inferType (() <$ pirFloated) =<< TC.getDefTypeCheckConfig ()
        -- letmerge is not necessary for floating, but is a nice visual transformation
        pure $ LetMerge.letMerge pirFloated

letFloatInConservative :: TestNested
letFloatInConservative =
    testNested "letFloatIn/conservative" $
        map
            (goldenPirM goldenFloatTC pTerm)
            [ "avoid-floating-into-lam"
            , "avoid-floating-into-tyabs"
            ]
  where
    goldenFloatTC pir = rethrow . asIfThrown @(PIR.Error PLC.DefaultUni PLC.DefaultFun ()) $ do
        let pirFloated = runQuote $ LetFloatIn.floatTerm def False pir
        -- make sure the floated result typechecks
        _ <- runQuoteT . flip inferType (() <$ pirFloated) =<< TC.getDefTypeCheckConfig ()
        -- letmerge is not necessary for floating, but is a nice visual transformation
        pure $ LetMerge.letMerge pirFloated

letFloatInRelaxed :: TestNested
letFloatInRelaxed =
    testNested "letFloatIn/relaxed" $
        map
            (goldenPirM goldenFloatTC pTerm)
            [ "avoid-floating-into-RHS"
            , "avoid-moving-strict-nonvalue-bindings"
            , "cannot-float-into-app"
            , "datatype1"
            , "datatype2"
            , "float-into-fun-and-arg-1"
            , "float-into-fun-and-arg-2"
            , "float-into-lam1"
            , "float-into-lam2"
            , "float-into-RHS"
            , "float-into-tyabs1"
            , "float-into-tyabs2"
            , "float-into-constr"
            , "float-into-case-arg"
            , "float-into-case-branch"
            , "type"
            ]
  where
    goldenFloatTC pir = rethrow . asIfThrown @(PIR.Error PLC.DefaultUni PLC.DefaultFun ()) $ do
        let pirFloated = runQuote $ LetFloatIn.floatTerm def True pir
        -- make sure the floated result typechecks
        _ <- runQuoteT . flip inferType (() <$ pirFloated) =<< TC.getDefTypeCheckConfig ()
        -- letmerge is not necessary for floating, but is a nice visual transformation
        pure $ LetMerge.letMerge pirFloated

recSplit :: TestNested
recSplit =
    testNested "recSplit" $
        map
            (goldenPir (RecSplit.recSplit . runQuote . PLC.rename) pTerm)
            [ "truenonrec"
            , "mutuallyRecursiveTypes"
            , "mutuallyRecursiveValues"
            , "selfrecursive"
            , "small"
            , "big"
            ]

instance Semigroup PLC.SrcSpan where
    sp1 <> _ = sp1

instance Monoid PLC.SrcSpan where
    mempty = initialSrcSpan ""

inline :: TestNested
inline =
    testNested "inline" $
        map
            (goldenPir (runQuote . (Inline.inline mempty def <=< PLC.rename)) pTerm)
            [ "var"
            , "builtin"
            , "constant"
            , "transitive"
            , "tyvar"
            , "single"
            , "immediateVar"
            , "immediateApp"
            -- these tests are all let bindings of functions
            , "letFunConstInt" -- const fn fully applied (integer)
            , "letFunConstBool" -- const fn fully applied (bool)
            , "letFunConstMulti" -- multiple occurrences of a let binding of the const fn.
            , "letFunInFun" -- fully applied fn inside another let, single occurrence.
            , "letFunInFunMulti" -- fully applied fn inside another let, multiple occurrences.
            -- similar to "letFunInFunMulti" but all fns are fully applied.
            , "letTypeAppMulti"
            -- singe occurrence of a polymorphic id function that is fully applied
            , "letTypeApp"
            -- multiple occurrences of a polymorphic id function that IS fully applied
            , "letTypeAppMultiSat"
            -- multiple occurrences of a polymorphic id function that is NOT fully applied
            , "letTypeAppMultiNotSat"
            , "letApp" -- single occurrence of a function application in rhs
            -- multiple occurrences of a function application in rhs with not acceptable body
            , "letAppMultiNotAcceptable"
            , "letOverApp" -- over-application of a function, single occurrence
            , "letOverAppMulti" -- multiple occurrences of an over-application of a function
            -- multiple occurrences of an over-application of a function with type arguments
            , "letOverAppType"
            , "letOverAppType2"
            , "letOverAppType3"
            , "letNonPure" -- multiple occurrences of a non-pure binding
            , "letNonPureMulti"
            , "letNonPureMultiStrict"
            ]

computeArityTest :: TestNested
computeArityTest = testNested "computeArityTest" $
        map
            (goldenPir (computeArity . runQuote . PLC.rename) pTerm)
            [ "var" -- from inline tests, testing let terms
            , "tyvar"
            , "single"
            , "immediateVar"
            -- from beta tests, testing app terms
            , "absapp" -- type application
            , "multiapp"
            , "multilet"
            , "lamAbs3" -- 3 term lambdas
            , "lamAbsApp" -- 3 term lambdas and the function body is an application
            , "ifError" -- more complicated body
            , "tyAbs" -- type lambda abstraction
            , "tyAbs2" -- 2 type lambda abstractions
            , "tyAbs2Arrow" -- type lambda abstraction with an arrow kind
            , "tyAbsInterleaved" -- interleaving type and term lambda abstractions
            ]

beta :: TestNested
beta =
    testNested "beta" $
        map
            (goldenPir (Beta.beta . runQuote . PLC.rename) pTerm)
            [ "lamapp"
            , "lamapp2"
            , "absapp"
            , "multiapp"
            , "multilet"
            ]

unwrapCancel :: TestNested
unwrapCancel =
    testNested "unwrapCancel" $
        map
            (goldenPir Unwrap.unwrapCancel pTerm)
            -- Note: these examples don't typecheck, but we don't care
            [ "unwrapWrap"
            , "wrapUnwrap"
            ]

deadCode :: TestNested
deadCode =
    testNested "deadCode" $
        map
            (goldenPir (runQuote . DeadCode.removeDeadBindings def) pTerm)
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
