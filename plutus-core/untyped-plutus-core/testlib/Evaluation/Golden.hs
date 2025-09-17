-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Evaluation.Golden
    ( test_golden
    , namesAndTests
    ) where

import Prelude hiding (even)

import PlutusCore.StdLib.Data.Bool
import PlutusCore.StdLib.Data.Function
import PlutusCore.StdLib.Data.Nat
import PlutusCore.StdLib.Data.ScottList
import PlutusCore.StdLib.Meta
import PlutusCore.StdLib.Meta.Data.Tuple
import PlutusCore.StdLib.Type

import PlutusCore
import PlutusCore.Compiler.Erase
import PlutusCore.Evaluation.Machine.Ck
import PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import PlutusCore.Generators.Hedgehog.Interesting
import PlutusCore.MkPlc
import PlutusCore.Pretty
import UntypedPlutusCore.Evaluation.Machine.Cek

import Control.Monad.Except
import Data.Bifunctor
import Data.ByteString.Lazy qualified as BSL
import Data.Default.Class (Default (def))
import Data.Text (Text)
import Data.Text.Encoding (encodeUtf8)
import Test.Tasty
import Test.Tasty.Golden

-- (con integer)
integer :: uni `HasTypeLevel` Integer => Type TyName uni ()
integer = mkTyBuiltin @_ @Integer ()

-- (con string)
string :: uni `HasTypeLevel` Text => Type TyName uni ()
string = mkTyBuiltin @_ @Text ()

evenAndOdd :: uni `HasTypeAndTermLevel` Bool => Tuple (Term TyName Name uni fun) uni ()
evenAndOdd = runQuote $ do
    let nat = _recursiveType natData

    evenn <- freshName "even"
    oddd  <- freshName "odd"

    let eoFunc b recc = do
          n <- freshName "n"
          pure $
              LamAbs () n nat $
              Apply () (Apply () (TyInst () (Unwrap () (Var () n)) bool) b) $ Var () recc

    evenF <- FunctionDef () evenn (FunctionType () nat bool) <$> eoFunc true oddd
    oddF  <- FunctionDef () oddd  (FunctionType () nat bool) <$> eoFunc false evenn

    getMutualFixOf () (fixN 2 fixBy) [evenF, oddF]

even :: uni `HasTypeAndTermLevel` Bool => Term TyName Name uni fun ()
even = runQuote $ tupleTermAt () 0 evenAndOdd

evenAndOddList :: Tuple (Term TyName Name uni fun) uni ()
evenAndOddList = runQuote $ do
    let list = _recursiveType listData
        nat  = _recursiveType natData
        listNat = TyApp () list nat

    evenn <- freshName "even"
    oddd  <- freshName "odd"

    let eoFunc recc = do
          l <- freshName "l"
          pure $
              LamAbs () l listNat $
              Apply () (
                  Apply () (TyInst () (Unwrap () (Var () l)) listNat)
                  (TyInst() nil nat))
              recc

    evenF <- FunctionDef () evenn (FunctionType () listNat listNat) <$> do
        h <- freshName "head"
        t <- freshName "tail"
        eoFunc $
            LamAbs () h nat $
            LamAbs () t listNat $
            Apply () (Apply () (TyInst () cons nat) (Var () h)) $
            Apply () (Var () oddd) (Var () t)

    oddF <- FunctionDef () oddd (FunctionType () listNat listNat) <$> do
        h <- freshName "head"
        t <- freshName "tail"
        eoFunc $
            LamAbs () h nat $
            LamAbs () t listNat $
            Apply () (Var () evenn) (Var () t)

    getMutualFixOf () (fixN 2 fixBy) [evenF, oddF]

evenList :: Term TyName Name uni fun ()
evenList = runQuote $ tupleTermAt () 0 evenAndOddList

smallNatList :: Term TyName Name uni fun ()
smallNatList = metaListToScottList nat nats where
    nats = Prelude.map metaIntegerToNat [1,2,3]
    nat = _recursiveType natData

polyError :: Term TyName Name uni fun ()
polyError = runQuote $ do
    a <- freshTyName "a"
    pure $ TyAbs () a (Type ()) $ Error () (TyVar () a)

-- | For checking that evaluating a term to a non-constant results in all remaining variables
-- being instantiated.
closure :: uni `HasTypeAndTermLevel` Integer => Term TyName Name uni fun ()
closure = runQuote $ do
    i <- freshName "i"
    j <- freshName "j"
    pure
        . Apply () (LamAbs () i integer . LamAbs () j integer $ Var () i)
        $ mkConstant @Integer () 1

{- Tests for evaluation of builtins.  The main point of these is to check that
   interleaving of term and type arguments is correct, but a number of other
   tests checking that ill-typed builtins execute successfully (because types
   are ignored at runtime) are included.  At the moment the only polymorphic
   builtin we have is ifThenElse.

   We test a number of terms to check whether they typecheck and whether they
   evaluate without error.  There are four possible outcomes:

     * The term typechecks and evaluates successfully
     * The term typechecks and evaluation fails
     * The term is ill-typed but still evaluates successfully
     * The term is ill-typed and evaluation fails

   We'll denote these outcomes by WellTypedRuns, WellTypedFails, IllTypedRuns, and IllTypedFails
   respectively; each test is labelled with one of these.
-}

-- Various components that we'll use to build larger terms for testing

lte :: Term TyName Name DefaultUni DefaultFun ()
lte = Builtin () LessThanEqualsInteger

eleven :: Term TyName Name DefaultUni DefaultFun ()
eleven = mkConstant @Integer () 11

twentytwo :: Term TyName Name DefaultUni DefaultFun ()
twentytwo = mkConstant @Integer () 22

stringResultTrue :: Term TyName Name DefaultUni DefaultFun ()
stringResultTrue = mkConstant @Text () "11 <= 22"

stringResultFalse :: Term TyName Name DefaultUni DefaultFun ()
stringResultFalse = mkConstant @Text () "¬(11 <= 22)"

-- 11 <= 22
lteExpr :: Term TyName Name DefaultUni DefaultFun ()
lteExpr = mkIterAppNoAnn lte [eleven, twentytwo]


-- Various combinations of (partial) instantiation/application for ifThenElse

-- (builtin ifThenElse) : WellTypedRuns
ite :: Term TyName Name DefaultUni DefaultFun ()
ite = Builtin () IfThenElse

-- { (builtin ifThenElse) t }
iteAt :: Type TyName DefaultUni () -> Term TyName Name DefaultUni DefaultFun ()
iteAt = TyInst () ite

-- [ (builtin ifThenElse) (11<=22) ] : IllTypedFails (ifThenElse isn't
-- instantiated: type expected, term supplied.)
iteUninstantiatedWithCond :: Term TyName Name DefaultUni DefaultFun ()
iteUninstantiatedWithCond  = Apply () ite lteExpr

-- (builtin ifThenElse) (11<=22) "11 <= 22" "¬(11<=22)" : IllTypedFails (no
-- instantiation)
iteUninstantiatedFullyApplied :: Term TyName Name DefaultUni DefaultFun ()
iteUninstantiatedFullyApplied = mkIterAppNoAnn ite [lteExpr, stringResultTrue, stringResultFalse]

-- { (builtin ifThenElse) (con integer) } : WellTypedRuns
iteAtInteger :: Term TyName Name DefaultUni DefaultFun ()
iteAtInteger = iteAt integer

-- [ { (builtin ifThenElse) (con integer) } (11<=22)] : WellTypedRuns
iteAtIntegerWithCond :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerWithCond = Apply () iteAtInteger lteExpr

-- [ { (builtin ifThenElse) (con integer) } "11 <= 22" "¬(11<=22)" ] :
-- IllTypedRuns.  This is ill-typed because the first term argument is a string
-- and a boolean is expected.
-- At execution time the default unlifting mode (Deferred) dictates
-- that builtin has to be saturated before it can runtime check for its types.
-- This is contrary to the older unlfiting mode (Immediate)
-- the builtin application machinery unlifts an argument and checks its type the moment it gets it,
-- without waiting for full saturation.
iteAtIntegerWrongCondTypeUnSat :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerWrongCondTypeUnSat = mkIterAppNoAnn iteAtInteger [stringResultTrue, stringResultFalse]

-- [ { (builtin ifThenElse) (con integer) } "11 <= 22" "¬(11<=22)" "¬(11<=22)" ] :
-- IllTypedFails. This is ill-typed because the first term argument is a string
-- and a boolean is expected. At execution time,
-- the default unlifting mode (Deferred) can finally check for the types of the arguments to
-- builtin function, since the builtin application is fully saturated. The older unlifting
-- mode would also fail, but earlier before the builtin call got even saturated, see `iteAtIntegerWrongCondTypeUnSat`.
iteAtIntegerWrongCondTypeSat :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerWrongCondTypeSat = mkIterAppNoAnn iteAtInteger [stringResultTrue, stringResultFalse, stringResultFalse]

-- [ { (builtin ifThenElse) (con integer) } (11<=22) "11 <= 22" "¬(11<=22)" ] :
-- IllTypedRuns.  We're instantiating at `integer` but returning a string: at
-- execution time we only check that type instantiations and term arguments are
-- correctly interleaved, not that instantiations are correct.
iteAtIntegerFullyApplied :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerFullyApplied = mkIterAppNoAnn iteAtIntegerWithCond [stringResultTrue, stringResultFalse]

-- [ (builtin divideInteger) 1 0 ] : WellTypedFails. Division by zero.
diFullyApplied :: Term TyName Name DefaultUni DefaultFun ()
diFullyApplied = mkIterAppNoAnn (Builtin () DivideInteger)
    [ mkConstant @Integer () 1
    , mkConstant @Integer () 0
    ]

-- { (builtin ifThenElse) (con string) } : WellTypedRuns
iteAtString :: Term TyName Name DefaultUni DefaultFun ()
iteAtString = iteAt string

-- [ { (builtin ifThenElse) (con string) } (11<=22) ] : WellTypedRuns
iteAtStringWithCond :: Term TyName Name DefaultUni DefaultFun ()
iteAtStringWithCond = Apply () iteAtString lteExpr

-- [ { (builtin ifThenElse) (con string) } (11<=22) 33 "abc" ] : IllTypedRuns
-- This is ill-typed because the first branch is of type @integer@ and the second branch is of type
-- @string@. It still runs succefully, because even in typed world (the CK machine) we don't look
-- at types at runtime.
iteAtStringWithCondWithIntegerWithString :: Term TyName Name DefaultUni DefaultFun ()
iteAtStringWithCondWithIntegerWithString = mkIterAppNoAnn iteAtStringWithCond
    [ mkConstant @Integer () 33
    , mkConstant @Text () "abc"
    ]

-- [ { (builtin ifThenElse)  (con string) } (11<=22) "11 <= 22" "¬(11<=22)" ] : WellTypedRuns
iteAtStringFullyApplied :: Term TyName Name DefaultUni DefaultFun ()
iteAtStringFullyApplied = mkIterAppNoAnn iteAtStringWithCond [stringResultTrue, stringResultFalse]

-- { builtin ifThenElse (fun (con integer) (con integer)) } : WellTypedRuns
iteAtIntegerArrowInteger :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerArrowInteger = iteAt (TyFun () integer integer)

-- [ { (builtin ifThenElse) (fun (con integer) (con integer)) } (11<=22) ] : WellTypedRuns
iteAtIntegerArrowIntegerWithCond :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerArrowIntegerWithCond = Apply () iteAtIntegerArrowInteger lteExpr

-- [ { (builtin ifThenElse) (fun (con integer) (con integer)) } (11<=22) (11 *) (22 -)] :
-- WellTypedRuns (returns a function of type int -> int)
iteAtIntegerArrowIntegerApplied1 ::  Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerArrowIntegerApplied1 =  mkIterAppNoAnn
                                   iteAtIntegerArrowInteger
                                   [ lteExpr
                                   , Apply () (Builtin () MultiplyInteger) eleven
                                   , Apply () (Builtin () SubtractInteger) twentytwo
                                   ]

-- [ { (builtin ifThenElse) (fun (con integer) (con integer)) } (11<=22) (*) (-)] :
-- IllTypedRuns (int -> int -> int instead of int -> int).
iteAtIntegerArrowIntegerApplied2 ::  Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerArrowIntegerApplied2 =  mkIterAppNoAnn
                                    iteAtIntegerArrowInteger
                                    [ lteExpr
                                    , Builtin () MultiplyInteger
                                    , Builtin () SubtractInteger
                                    ]

-- [ { (builtin ifThenElse) (fun (con integer) (con integer)) } (11<=22) (11 *) (22 -) 22] :
-- WellTypedRuns (ifThenElse returns a function which is then applied to a constant).
iteAtIntegerArrowIntegerAppliedApplied :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerArrowIntegerAppliedApplied =  Apply () iteAtIntegerArrowIntegerApplied1 twentytwo

-- { (builtin ifThenElse) (lam a . a -> a) } : IllTypedRuns.
-- Evaluation should succeed, but typechecking should fail with a kind error.
-- The built-in function machinery does allow builtins which are polymorphic
-- over higher-kinded types, but `ifThenElse` can only be instantiated with
-- types of kind *.
iteAtHigherKind :: Term TyName Name DefaultUni DefaultFun ()
iteAtHigherKind = iteAt (TyLam () a (Type ()) aArrowA)
    where a = TyName (Name "a" (Unique 0))
          aArrowA = TyFun () (TyVar () a) (TyVar () a)

-- [ { (builtin ifThenElse) (lam a . a -> a) } (11<=22) ] : IllTypedRuns
-- (illegal kind)
iteAtHigherKindWithCond :: Term TyName Name DefaultUni DefaultFun ()
iteAtHigherKindWithCond = Apply () iteAtHigherKind lteExpr

-- [ {(builtin ifThenElse) (lam a . a -> a) } (11<=22) "11 <= 22" "¬(11<=22) ]" :
-- IllTypedRuns (illegal kind)
iteAtHigherKindFullyApplied :: Term TyName Name DefaultUni DefaultFun ()
iteAtHigherKindFullyApplied = mkIterAppNoAnn (Apply () iteAtHigherKind lteExpr) [stringResultTrue, stringResultFalse]

-- { {(builtin ifThenElse) integer} integer } : IllTypedFails (instantiated twice).
iteAtIntegerAtInteger :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerAtInteger = TyInst () iteAtInteger integer

-- { [ { (builtin ifThenElse) integer } (11<=22)] integer } : IllTypedFails
-- (term expected, type supplied).
iteTypeTermType :: Term TyName Name DefaultUni DefaultFun ()
iteTypeTermType = TyInst () iteAtIntegerWithCond string


-- Various attempts to instantiate the MultiplyInteger builtin. This is not
-- polymorphic, so most should fail (and we're checking that they _do_ fail).

-- (builtin multiplyInteger) (not tested)
mul ::  Term TyName Name DefaultUni DefaultFun ()
mul = Builtin () MultiplyInteger

-- [ [ (builtin multiplyInteger) 11 ] 22 ] : WellTypedRuns
mulOK :: Term TyName Name DefaultUni DefaultFun ()
mulOK = Apply () (Apply () mul eleven) twentytwo

-- [ [ { (builtin multiplyInteger) string } 11 ] 22 ]: IllTypedFails
mulInstError1 :: Term TyName Name DefaultUni DefaultFun ()
mulInstError1 = Apply () (Apply () (TyInst () mul string) eleven) twentytwo

-- [ [ { (builtin multiplyInteger) 11 ] string } 22 ]: IllTypedFails
mulInstError2 :: Term TyName Name DefaultUni DefaultFun ()
mulInstError2 = Apply () (TyInst () (Apply () mul eleven) string) twentytwo

-- { [ [ (builtin multiplyInteger) 11 ] 22 ] string } : IllTypedFails
mulInstError3 :: Term TyName Name DefaultUni DefaultFun ()
mulInstError3 = TyInst () (Apply () (Apply () mul eleven) twentytwo) string

tag1 :: Term TyName Name DefaultUni DefaultFun ()
tag1 = Constr () (TySOP () [[integer], [string]]) 0 [mkConstant @Integer () 1]

tag2 :: Term TyName Name DefaultUni DefaultFun ()
tag2 = Constr () (TySOP () [[integer], [string]]) 1 [mkConstant @Text () "hello"]

tagProd1 :: Term TyName Name DefaultUni DefaultFun ()
tagProd1 = Constr () (TySOP () [[integer, integer, integer], [string]]) 0
    [mkConstant @Integer () 1, mkConstant @Integer () 2, mkConstant @Integer () 4]

case1 :: Term TyName Name DefaultUni DefaultFun ()
case1 = runQuote $ do
    a <- freshName "a"
    let branch1 = LamAbs () a integer (Var () a)
        branch2 = LamAbs () a string (mkConstant @Integer () 2)
    pure $ Case () integer tag1 [branch1, branch2]

case2 :: Term TyName Name DefaultUni DefaultFun ()
case2 = runQuote $ do
    a <- freshName "a"
    let branch1 = LamAbs () a integer (Var () a)
        branch2 = LamAbs () a string (mkConstant @Integer () 2)
    pure $ Case () integer tag2 [branch1, branch2]

case3 :: Term TyName Name DefaultUni DefaultFun ()
case3 = runQuote $ do
    a <- freshName "a"
    let branch1 = LamAbs () a integer (mkConstant @Text () "no")
        branch2 = LamAbs () a string (Var () a)
    pure $ Case () string tag1 [branch1, branch2]

case4 :: Term TyName Name DefaultUni DefaultFun ()
case4 = runQuote $ do
    a <- freshName "a"
    let branch1 = LamAbs () a integer (mkConstant @Text () "no")
        branch2 = LamAbs () a string (Var () a)
    pure $ Case () string tag2 [branch1, branch2]

caseProd1 :: Term TyName Name DefaultUni DefaultFun ()
caseProd1 = runQuote $ do
    a <- freshName "a"
    b <- freshName "b"
    c <- freshName "c"
    let branch1 = LamAbs () a integer $ LamAbs () b integer $ LamAbs () c integer $
                    mkIterAppNoAnn (Builtin () SubtractInteger) [
                      mkIterAppNoAnn (Builtin () AddInteger) [Var () a, Var () b]
                      , Var () c
                      ]
        branch2 = LamAbs () a string (mkConstant @Integer () 2)
    pure $ Case () integer tagProd1 [branch1, branch2]

caseNoBranch :: Term TyName Name DefaultUni DefaultFun ()
caseNoBranch = Case () integer tag1 []

caseInteger :: Term TyName Name DefaultUni DefaultFun ()
caseInteger = Case () integer (mkConstant @Integer () 1) []

caseList :: Term TyName Name DefaultUni DefaultFun ()
caseList = runQuote $ do
  a <- freshName "a"
  b <- freshName "b"
  pure $
    Case () integer (mkConstant @[Integer] () [1])
      [ LamAbs () a integer $ LamAbs () b (mkTyBuiltin @_ @[Integer] ()) $ Var () a
      ]

caseNonTag :: Term TyName Name DefaultUni DefaultFun ()
caseNonTag = Case () integer (builtin () AddInteger) []

-- | For testing that an accidental exception will get caught.
headSingletonException :: Term TyName Name DefaultUni DefaultFun ()
headSingletonException
    = Apply () (TyInst () (Builtin () HeadList) $ mkTyBuiltin @_ @Bool ())
    $ mkConstant () [errorWithoutStackTrace "catch me if you can" :: Bool]

-- Running the tests

goldenVsPretty :: PrettyPlc a => String -> String -> a -> TestTree
goldenVsPretty extn name value =
    goldenVsString name ("untyped-plutus-core/test/Evaluation/Golden/" ++ name ++ extn) $
        pure . BSL.fromStrict . encodeUtf8 . render $ prettyPlcClassicSimple value

goldenVsEvaluatedCK :: String -> Term TyName Name DefaultUni DefaultFun () -> TestTree
goldenVsEvaluatedCK name
    = goldenVsPretty ".golden.plc" name
    . bimap (fmap eraseTerm) eraseTerm
    . evaluateCkNoEmit defaultBuiltinsRuntimeForTesting def

goldenVsEvaluatedCEK :: String -> Term TyName Name DefaultUni DefaultFun () -> TestTree
goldenVsEvaluatedCEK name
    = goldenVsPretty ".golden.uplc" name
    . evaluateCekNoEmit defaultCekParametersForTesting
    . eraseTerm

runTypecheck
    :: Term TyName Name DefaultUni DefaultFun ()
    -> Either (Error DefaultUni DefaultFun ()) (Normalized (Type TyName DefaultUni ()))
runTypecheck term =
  runQuoteT $ modifyError TypeErrorE $ do
    tcConfig <- getDefTypeCheckConfig ()
    inferType tcConfig term

goldenVsTypechecked :: String -> Term TyName Name DefaultUni DefaultFun () -> TestTree
goldenVsTypechecked name = goldenVsPretty ".golden.type" name . runTypecheck

goldenVsTypecheckedEvaluatedCK :: String -> Term TyName Name DefaultUni DefaultFun () -> TestTree
goldenVsTypecheckedEvaluatedCK name term =
    -- The CK machine can evaluate an ill-typed term to a well-typed one, so we check
    -- that the term is well-typed before checking that the type of the result is the
    -- one stored in the golden file (we could simply check the two types for equality,
    -- but since we're doing golden testing in this file, why not do it here as well).
    case (runTypecheck term, evaluateCkNoEmit defaultBuiltinsRuntimeForTesting def term) of
        (Right _, Right res) -> goldenVsTypechecked name res
        _                    -> testGroup name []

namesAndTests :: [(String, Term TyName Name DefaultUni DefaultFun ())]
namesAndTests =
   [ ("even2", Apply () even $ metaIntegerToNat 2)
   , ("even3", Apply () even $ metaIntegerToNat 3)
   , ("evenList", Apply () natSum $ Apply () evenList smallNatList)
   , ("polyError", polyError)
   , ("polyErrorInst", TyInst () polyError (mkTyBuiltin @_ @Integer ()))
   , ("closure", closure)
   , ("ite", ite)
   , ("iteUninstantiatedWithCond", iteUninstantiatedWithCond)
   , ("iteUninstantiatedFullyApplied", iteUninstantiatedFullyApplied)
   , ("iteAtInteger", iteAtInteger)
   , ("iteAtIntegerWithCond", iteAtIntegerWithCond)
   , ("iteAtIntegerWrongCondTypeUnSat", iteAtIntegerWrongCondTypeUnSat)
   , ("iteAtIntegerWrongCondTypeSat", iteAtIntegerWrongCondTypeSat)
   , ("iteAtIntegerFullyApplied", iteAtIntegerFullyApplied)
   , ("diFullyApplied", diFullyApplied)
   , ("iteAtString", iteAtString)
   , ("iteAtStringWithCond", iteAtStringWithCond)
   , ("iteAtStringWithCondWithIntegerWithString", iteAtStringWithCondWithIntegerWithString)
   , ("iteAtStringFullyApplied", iteAtStringFullyApplied)
   , ("iteAtIntegerArrowInteger", iteAtIntegerArrowInteger)
   , ("iteAtIntegerArrowIntegerWithCond", iteAtIntegerArrowIntegerWithCond)
   , ("iteAtIntegerArrowIntegerApplied1", iteAtIntegerArrowIntegerApplied1)
   , ("iteAtIntegerArrowIntegerApplied2", iteAtIntegerArrowIntegerApplied2)
   , ("iteAtIntegerArrowIntegerAppliedApplied", iteAtIntegerArrowIntegerAppliedApplied)
   , ("iteAtHigherKind", iteAtHigherKind)
   , ("iteAtHigherKindWithCond", iteAtHigherKindWithCond)
   , ("iteAtHigherKindFullyApplied", iteAtHigherKindFullyApplied)
   , ("iteAtIntegerAtInteger", iteAtIntegerAtInteger)
   , ("iteTypeTermType", iteTypeTermType)
   , ("mulOK", mulOK)
   , ("mulInstError1", mulInstError1)
   , ("mulInstError2", mulInstError2)
   , ("mulInstError3", mulInstError3)
   , ("tag1", tag1)
   , ("tag2", tag2)
   , ("tagProd1", tagProd1)
   , ("case1", case1)
   , ("case2", case2)
   , ("case3", case3)
   , ("case4", case4)
   , ("caseProd1", caseProd1)
   , ("caseNoBranch", caseNoBranch)
   , ("caseInteger", caseInteger)
   , ("caseList", caseList)
   , ("caseNonTag", caseNonTag)
   ]

-- | An extension of 'namesAndTests' that only works with the CEK machine and not the CK one.
namesAndTestsCek :: [(String, Term TyName Name DefaultUni DefaultFun ())]
namesAndTestsCek
    = ("headSingletonException", headSingletonException)
    : namesAndTests

test_golden :: TestTree
test_golden = testGroup "golden"
              [ testGroup "CK"  $ fmap (uncurry goldenVsEvaluatedCK)  namesAndTests
              -- The CEK tests have been added to the plutus-conformance tests
              -- (mostly renamed since there's no instantation, and with some
              -- duplicates removed).  We should also add the typed tests to the
              -- conformance suite and remove them from here once we've done
              -- that.
              , testGroup "CEK" $ fmap (uncurry goldenVsEvaluatedCEK) namesAndTestsCek
              , testGroup "Typechecking" $ fmap (uncurry goldenVsTypechecked) namesAndTestsCek
              , testGroup "Typechecking CK output" $ fmap (uncurry goldenVsTypecheckedEvaluatedCK) namesAndTests
              ]
