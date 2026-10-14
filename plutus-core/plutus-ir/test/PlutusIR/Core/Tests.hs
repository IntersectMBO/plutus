{-# LANGUAGE OverloadedStrings #-}

module PlutusIR.Core.Tests where

import PlutusCore qualified as PLC
import PlutusCore.Pretty
import PlutusCore.Version (plcVersion120)
import PlutusIR
import PlutusIR.Parser (pTerm)
import PlutusIR.Test

import Test.Tasty
import Test.Tasty.Extras
import Test.Tasty.HUnit

import Control.DeepSeq (NFData, rnf)
import Control.Exception (ErrorCall, evaluate, try)
import Data.Functor
import Data.List.NonEmpty (NonEmpty (..))
import Data.Word (Word8)
import PlutusCore.Flat
import PlutusCore.Flat.Bits (asBytes, bits)

test_prettyprinting :: TestTree
test_prettyprinting =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Core", "prettyprinting"] $
    map
      (goldenPir id pTerm)
      [ "basic"
      , "maybe"
      ]

test_prettyprintingReadable :: TestTree
test_prettyprintingReadable =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Core", "prettyprintingReadable"] $
    map
      (goldenPirDoc prettyReadableSimple pTerm)
      [ "basic"
      , "maybe"
      , "letInLet"
      , "letDep"
      , "listMatch"
      , "idleAll"
      , "some"
      , "even3"
      , "stupidZero"
      , "mutuallyRecursiveValues"
      , "errorBinding"
      , "some"
      , "stupidZero"
      , "recursiveTypeBind"
      ]

test_serialization :: TestTree
test_serialization =
  runTestNested ["plutus-ir", "test", "PlutusIR", "Core", "serialization"] $
    map
      (goldenPir roundTripPirTerm pTerm)
      [ "serializeBasic"
      , "serializeMaybePirTerm"
      , "serializeEvenOdd"
      , "serializeListMatch"
      ]

roundTripPirTerm
  :: Term TyName Name PLC.DefaultUni PLC.DefaultFun a
  -> Term TyName Name PLC.DefaultUni PLC.DefaultFun ()
roundTripPirTerm = decodeOrError . unflat . flat . void
  where
    decodeOrError (Right tm) = tm
    decodeOrError (Left err) = error (show err)

test_flatStaticEncoding :: TestTree
test_flatStaticEncoding =
  testGroup
    "Flat stable encoding"
    [ testCase "NonRec" $ flatBytes NonRec @?= [0]
    , testCase "Rec" $ flatBytes Rec @?= [128]
    , testCase "NonStrict" $ flatBytes NonStrict @?= [0]
    , testCase "Strict" $ flatBytes Strict @?= [128]
    ]
  where
    flatBytes :: Flat a => a -> [Word8]
    flatBytes = asBytes . bits

-- | 'rnf' on a PIR program must reach annotations, nested bindings and datatype declarations.
test_nfData :: TestTree
test_nfData =
  testGroup
    "NFData"
    [ testCase "forces a complete program" $
        evaluate (rnf (program () [termBinding, typeBinding, datatypeBinding]))
    , testCase "forces program annotations" $
        assertDeferredError (program (error "program annotation") [termBinding])
    , testCase "forces nested binding annotations" $
        assertDeferredError (program () [TermBind (error "binding annotation") Strict declaration body])
    , testCase "forces term-binding strictness" $
        assertDeferredError (program () [TermBind () (error "strictness") declaration body])
    , testCase "forces variable-declaration types" $
        assertDeferredError (program () [TermBind () Strict (VarDecl () name (error "type")) body])
    , testCase "forces type-declaration kinds" $
        assertDeferredError (program () [TypeBind () (TyVarDecl () typeName (error "kind")) typ])
    , testCase "forces datatype constructor lists" $
        assertDeferredError
          (program () [DatatypeBind () (Datatype () typeDeclaration [] name [error "constructor"])])
    , testCase "forces nested term arguments" $
        assertDeferredError (program () [TermBind () Strict declaration (Apply () body (error "argument"))])
    ]
  where
    name = PLC.Name "value" (PLC.Unique 0)
    typeName = PLC.TyName (PLC.Name "type" (PLC.Unique 1))
    typ = TyVar () typeName
    body = Var () name
    declaration = VarDecl () name typ
    typeDeclaration = TyVarDecl () typeName (Type ())
    termBinding = TermBind () Strict declaration body
    typeBinding = TypeBind () typeDeclaration typ
    datatypeBinding = DatatypeBind () (Datatype () typeDeclaration [] name [declaration])
    program
      :: ()
      -> [Binding TyName Name PLC.DefaultUni PLC.DefaultFun ()]
      -> Program TyName Name PLC.DefaultUni PLC.DefaultFun ()
    program annotation bindings =
      Program annotation plcVersion120 (Let () NonRec (termBinding :| bindings) body)

-- | Assert that 'rnf' reaches an 'error' planted in the value.
assertDeferredError :: NFData value => value -> Assertion
assertDeferredError value = do
  result <- try (evaluate (rnf value)) :: IO (Either ErrorCall ())
  case result of
    Left _ -> pure ()
    Right () -> assertFailure "NFData did not force a deferred error"
