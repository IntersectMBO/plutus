{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module TransformSpec (transform) where

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
        , knownCon
        , recSplit
        , inline
        , nameCapture
        , beta
        , unwrapCancel
        , deadCode
        , retainedSize
        , rename
        , evaluateBuiltins
        , commuteDefaultFun
        , strictifyBindings
        ]

thunkRecursions :: TestNested
thunkRecursions =
    testNested "thunkRecursions" $
        map
            (goldenPir (ThunkRec.thunkRecursions def) pTerm)
            [ "listFold"
            , "listFoldTrace"
            , "monoMap"
            , "errorBinding"
            , "mutuallyRecursiveValues"
            , "preserveEffectOrder"
            , "preserveStrictness"
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

knownCon :: TestNested
knownCon =
    testNested "knownCon" $
        map
            (goldenPirM goldenKnownConTC pTerm)
            [ "applicative"
            , "bool"
            , "list"
            , "maybe-just"
            , "maybe-just-unsaturated"
            , "maybe-nothing"
            , "pair"
            ]
  where
    goldenKnownConTC pir = rethrow . asIfThrown @(PIR.Error PLC.DefaultUni PLC.DefaultFun ()) $ do
        let simplified = runQuote $ KnownCon.knownCon pir
        -- make sure the result typechecks
        _ <- runQuoteT . flip inferType (() <$ simplified) =<< TC.getDefTypeCheckConfig ()
        pure simplified

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

-- | Tests of the inliner, include global uniqueness test.
inline :: TestNested
inline =
    let goldenInlineUnique :: Term TyName Name PLC.DefaultUni PLC.DefaultFun PLC.SrcSpan ->
            IO (Term TyName Name PLC.DefaultUni PLC.DefaultFun PLC.SrcSpan)
        goldenInlineUnique pir =
            rethrow . asIfThrown @(UniqueError PLC.SrcSpan) $ do
                let pirInlined = runQuote $ do
                        renamed <- PLC.rename pir
                        Inline.inline mempty def renamed
                -- Make sure the inlined term is globally unique.
                _ <- checkUniques pirInlined
                pure pirInlined
    in
    testNested "inline" $
        map
            (goldenPirM goldenInlineUnique pTerm)
            [ "var"
            , "builtin"
            , "callsite-non-trivial-body"
            , "constant"
            , "transitive"
            , "tyvar"
            , "single"
            , "immediateVar"
            , "immediateApp"
            , "firstEffectfulTerm1"
            , "firstEffectfulTerm2"
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
            , "letTypeApp2" -- multiple occurrences of a function with type application
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
            , "letNonPure" -- multiple occurrences of a non-pure binding
            , "letNonPureMulti"
            , "letNonPureMultiStrict"
            , "rhs-modified"
            , "partiallyApp"
            , "effectfulBuiltinArg"
            ]

-- | Check whether a term is globally unique.
checkUniques :: (Ord a, MonadError (UniqueError a) m) => Term TyName Name uni fun a -> m ()
checkUniques =
    Uniques.checkTerm (\case { MultiplyDefined{} -> True; _ -> False})

-- | Tests that the inliner doesn't incorrectly capture variable names.
nameCapture :: TestNested
nameCapture =
    let goldenNameCapture :: Term TyName Name PLC.DefaultUni PLC.DefaultFun PLC.SrcSpan ->
            IO String
        goldenNameCapture pir =
            rethrow . asIfThrown @(UniqueError PLC.SrcSpan) $ do
                let pirInlined = runQuote $ do
                        renamed <- PLC.rename pir
                        Inline.inline mempty def renamed
                -- Make sure the inlined term is globally unique.
                _ <- checkUniques pirInlined
                pure . render $ prettyPirReadable pirInlined
    in
    testNested "nameCapture" $
        map
            (goldenPirMUnique goldenNameCapture pTerm)
            [ "nameCapture"]

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

evaluateBuiltins :: TestNested
evaluateBuiltins =
    testNested "evaluateBuiltins" $
        map
            (goldenPir (EvaluateBuiltins.evaluateBuiltins True def def) pTerm)
            [ "addInteger"
            , "ifThenElse"
            , "trace"
            , "failingBuiltin"
            , "nonConstantArg"
            , "overApplication"
            , "underApplication"
            ]

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
