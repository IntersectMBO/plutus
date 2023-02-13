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
import PlutusIR.Transform.Inline.UnconditionalInline qualified as UInline
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
transform = testNested "transform" [
    thunkRecursions
    , nonStrict
    , letFloatOut
    , letFloatIn
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
    $ map (goldenPir (ThunkRec.thunkRecursions def) pTerm)
    [ "listFold"
    , "monoMap"
    , "errorBinding"
    ]

nonStrict :: TestNested
nonStrict = testNested "nonStrict"
    $ map (goldenPir (runQuote . NonStrict.compileNonStrictBindings False) pTerm)
    [ "nonStrict1"
    ]

letFloatOut :: TestNested
letFloatOut =
    testNested "letFloatOut"
    $ map (goldenPirM goldenFloatTC pTerm)
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
       let pirFloated = RecSplit.recSplit . LetFloatOut.floatTerm def . runQuote $ PLC.rename pir
       -- make sure the floated result typechecks
       _ <- runQuoteT . flip inferType (() <$ pirFloated) =<< TC.getDefTypeCheckConfig ()
       -- letmerge is not necessary for floating, but is a nice visual transformation
       pure $ LetMerge.letMerge pirFloated

letFloatIn :: TestNested
letFloatIn =
    testNested "letFloatIn"
    $ map (goldenPirM goldenFloatTC pTerm)
  [ "avoid-floating-into-lam"
  , "avoid-floating-into-RHS"
  , "avoid-moving-strict-nonvalue-bindings"
  , "cannot-float-into-app"
  , "float-into-fun-and-arg-1"
  , "float-into-fun-and-arg-2"
  , "float-into-lam"
  , "float-into-RHS"
  , "float-into-tylam"
  ]
 where
   goldenFloatTC pir = rethrow . asIfThrown @(PIR.Error PLC.DefaultUni PLC.DefaultFun ()) $ do
       let pirFloated = runQuote $ LetFloatIn.floatTerm def pir
       -- make sure the floated result typechecks
       _ <- runQuoteT . flip inferType (() <$ pirFloated) =<< TC.getDefTypeCheckConfig ()
       -- letmerge is not necessary for floating, but is a nice visual transformation
       pure $ LetMerge.letMerge pirFloated

recSplit :: TestNested
recSplit =
    testNested "recSplit"
    $ map (goldenPir (RecSplit.recSplit . runQuote . PLC.rename) pTerm)
  [
    "truenonrec"
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
    testNested "inline"
    $ map (goldenPir (runQuote . (UInline.inline mempty def <=< PLC.rename)) $ pTerm)
    [ "var"
    , "builtin"
    , "constant"
    , "transitive"
    , "tyvar"
    , "single"
    , "immediateVar"
    , "immediateApp"
    ]


beta :: TestNested
beta =
    testNested "beta"
    $ map (goldenPir (Beta.beta . runQuote . PLC.rename) pTerm)
    [ "lamapp"
    , "lamapp2"
    , "absapp"
    , "multiapp"
    , "multilet"
    ]

unwrapCancel :: TestNested
unwrapCancel =
    testNested "unwrapCancel"
    $ map (goldenPir Unwrap.unwrapCancel pTerm)
    -- Note: these examples don't typecheck, but we don't care
    [ "unwrapWrap"
    , "wrapUnwrap"
    ]

deadCode :: TestNested
deadCode =
    testNested "deadCode"
    $ map (goldenPir (runQuote . DeadCode.removeDeadBindings def) pTerm)
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
    $ map (goldenPir renameAndAnnotate pTerm)
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
            . RetainedSize.annotateWithRetainedSize def
            . runQuote
            . PLC.rename

rename :: TestNested
rename =
    testNested "rename"
    $ map (goldenPir (PLC.AttachPrettyConfig debugConfig . runQuote . PLC.rename) pTerm)
    [ "allShadowedDataNonRec"
    , "allShadowedDataRec"
    , "paramShadowedDataNonRec"
    , "paramShadowedDataRec"
    ] where
        debugConfig = PLC.PrettyConfigClassic PLC.debugPrettyConfigName False
