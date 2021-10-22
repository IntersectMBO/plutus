{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module TransformSpec (transform) where

import           Common
import           PlcTestUtils
import           TestLib

import           PlutusCore.Quote

import qualified PlutusCore                         as PLC
import qualified PlutusCore.Pretty                  as PLC

import qualified PlutusIR.Analysis.RetainedSize     as RetainedSize
import           PlutusIR.Parser
import qualified PlutusIR.Transform.Beta            as Beta
import qualified PlutusIR.Transform.DeadCode        as DeadCode
import qualified PlutusIR.Transform.Inline          as Inline
import qualified PlutusIR.Transform.LetFloat        as LetFloat
import qualified PlutusIR.Transform.LetMerge        as LetMerge
import qualified PlutusIR.Transform.NonStrict       as NonStrict
import qualified PlutusIR.Transform.RecSplit        as RecSplit
import           PlutusIR.Transform.Rename          ()
import qualified PlutusIR.Transform.ThunkRecursions as ThunkRec
import qualified PlutusIR.Transform.Unwrap          as Unwrap

import           Control.Monad
import           PlutusIR.Error                     as PIR
import           PlutusIR.TypeCheck                 as TC
import           Text.Megaparsec.Pos


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
    $ map (goldenPir (runQuote . DeadCode.removeDeadBindings True) $ term @PLC.DefaultUni @PLC.DefaultFun)
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
