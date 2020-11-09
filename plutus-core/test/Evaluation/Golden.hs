{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Evaluation.Golden
    ( test_golden
    ) where

import           Prelude                                    hiding (even)

import           Language.PlutusCore.StdLib.Data.Bool
import           Language.PlutusCore.StdLib.Data.Function
import           Language.PlutusCore.StdLib.Data.List
import           Language.PlutusCore.StdLib.Data.Nat
import           Language.PlutusCore.StdLib.Meta
import           Language.PlutusCore.StdLib.Meta.Data.Tuple
import           Language.PlutusCore.StdLib.Type

import           Language.PlutusCore
import           Language.PlutusCore.Evaluation.Machine.Cek
import           Language.PlutusCore.Evaluation.Machine.Ck
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Pretty

import           Control.Monad.Except
import qualified Data.ByteString.Lazy                       as BSL
import           Data.Text.Encoding                         (encodeUtf8)
import           Test.Tasty
import           Test.Tasty.Golden

-- (con integer)
integer :: uni `Includes` Integer => Type TyName uni ()
integer = mkTyBuiltin @ Integer ()

-- (con string)
string :: uni `Includes` String => Type TyName uni ()
string = mkTyBuiltin @ String ()

evenAndOdd :: uni `Includes` Bool => Tuple (Term TyName Name uni fun) uni ()
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

even :: uni `Includes` Bool => Term TyName Name uni fun ()
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
smallNatList = metaListToList nat nats where
    nats = Prelude.map metaIntegerToNat [1,2,3]
    nat = _recursiveType natData

polyError :: Term TyName Name uni fun ()
polyError = runQuote $ do
    a <- freshTyName "a"
    pure $ TyAbs () a (Type ()) $ Error () (TyVar () a)

-- | For checking that evaluating a term to a non-constant results in all remaining variables
-- being instantiated.
closure :: uni `Includes` Integer => Term TyName Name uni fun ()
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
   builtin we have is ifThenElse. -}

-- Various components that we'll use to build larger terms for testing

lte :: Term TyName Name DefaultUni DefaultFun ()
lte = Builtin () LessThanEqInteger

eleven :: Term TyName Name DefaultUni DefaultFun ()
eleven = mkConstant @Integer () 11

twentytwo :: Term TyName Name DefaultUni DefaultFun ()
twentytwo = mkConstant @Integer () 22

stringResultTrue :: Term TyName Name DefaultUni DefaultFun ()
stringResultTrue = mkConstant @String () "11 <= 22"

stringResultFalse :: Term TyName Name DefaultUni DefaultFun ()
stringResultFalse = mkConstant @String () "¬(11 <= 22)"

-- 11 <= 22
lteExpr :: Term TyName Name DefaultUni DefaultFun ()
lteExpr = mkIterApp () lte [eleven, twentytwo]


-- Various combinations of (partial) instantiation/application for ifThenElse
-- These
-- (builtin ifThenElse)
ite :: Term TyName Name DefaultUni DefaultFun ()
ite = Builtin () IfThenElse

-- { (builtin ifThenElse) t }
iteAt :: Type TyName DefaultUni () -> Term TyName Name DefaultUni DefaultFun ()
iteAt ty = TyInst () ite ty

-- [ (builtin ifThenElse) (11<=22) ]: should fail to typecheck and fail during
-- execution because ifThenElse isn't instantiated: type expected, term supplied.
iteUninstantiatedWithCond :: Term TyName Name DefaultUni DefaultFun ()
iteUninstantiatedWithCond  = Apply () ite lteExpr

-- (builtin ifThenElse) (11<=22) "11 <= 22" "¬(11<=22)": should fail to
-- typecheck and fail during execution (no instantiation)
iteUninstantiatedFullyApplied :: Term TyName Name DefaultUni DefaultFun ()
iteUninstantiatedFullyApplied = mkIterApp () ite [lteExpr, stringResultTrue, stringResultFalse]

-- { (builtin ifThenElse) (con integer) }: should run and typecheck
iteAtInteger :: Term TyName Name DefaultUni DefaultFun ()
iteAtInteger = iteAt integer

-- [ { (builtin ifThenElse) (con integer) } (11<=22)]: should run and typecheck
iteAtIntegerWithCond :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerWithCond = Apply () iteAtInteger lteExpr

-- [ { (builtin ifThenElse) (con integer) } "11 <= 22" "¬(11<=22)" ] This is
-- ill-typed, since the first term argument is a string and a boolean is
-- expected.  However, it will execute successfully (and the result will be
-- ill-typed) because it's not saturated and so the built-in application
-- machinery will never see it.
iteAtIntegerWrongCondType :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerWrongCondType = mkIterApp () iteAtInteger [stringResultTrue, stringResultFalse]

-- [ { (builtin ifThenElse) (con integer) } (11<=22) "11 <= 22" "¬(11<=22)" ].
-- This should also succeed.  However it's ill-typed because we're instantiating
-- at `integer` but returning a string: at execution time we only check that
-- type instantiations and term arguments are correctly interleaved, not that
-- instantiations are correct.
iteAtIntegerFullyApplied :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerFullyApplied = mkIterApp () iteAtIntegerWithCond [stringResultTrue, stringResultFalse]

-- { (builtin ifThenElse) (con string) }: should run and typecheck
iteAtString :: Term TyName Name DefaultUni DefaultFun ()
iteAtString = iteAt string

-- [ { (builtin ifThenElse) (con string) } (11<=22) ]: should run and typecheck
iteAtStringWithCond :: Term TyName Name DefaultUni DefaultFun ()
iteAtStringWithCond = Apply () iteAtString lteExpr

-- [ { (builtin ifThenElse)  (con string) } (11<=22) "11 <= 22" "¬(11<=22)" ]: should run and typecheck
iteAtStringFullyApplied :: Term TyName Name DefaultUni DefaultFun ()
iteAtStringFullyApplied = mkIterApp () iteAtStringWithCond [stringResultTrue, stringResultFalse]

-- { builtin ifThenElse (fun (con integer) (con integer)) }
iteAtIntegerArrowInteger :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerArrowInteger = iteAt (TyFun () integer integer)

-- [ { (builtin ifThenElse) (fun (con integer) (con integer)) } (11<=22) ]: should run and typecheck
iteAtIntegerArrowIntegerWithCond :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerArrowIntegerWithCond = Apply () iteAtIntegerArrowInteger lteExpr

-- Should succeed and typecheck, returning a function of type int -> int
iteAtIntegerArrowIntegerApplied1 ::  Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerArrowIntegerApplied1 =  mkIterApp ()
                                   iteAtIntegerArrowInteger
                                   [ lteExpr
                                   , Apply () (Builtin () MultiplyInteger) eleven
                                   , Apply () (Builtin () SubtractInteger) twentytwo
                                   ]

-- Should succeed, but fail to typecheck (int -> int -> int instead of int -> int)
iteAtIntegerArrowIntegerApplied2 ::  Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerArrowIntegerApplied2 =  mkIterApp ()
                                    iteAtIntegerArrowInteger
                                    [ lteExpr
                                    , Builtin () MultiplyInteger
                                    , Builtin () SubtractInteger
                                    ]

-- Should succeed and typecheck: ifThenElse returns a function which is then applied to a constant.
iteAtIntegerArrowIntegerAppliedApplied :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerArrowIntegerAppliedApplied =  Apply () iteAtIntegerArrowIntegerApplied1 twentytwo

-- { (builtin ifThenElse) (lam a . a -> a) }
-- Evaluation should succeed, but typechecking should fail with a kind error.
-- The built-in function machinery does allow builtins which are polymorphic
-- over higher-kinded types, but `ifThenElse` can only be instantiated with
-- types of kind *.
iteAtHigherKind :: Term TyName Name DefaultUni DefaultFun ()
iteAtHigherKind = iteAt (TyLam () a (Type ()) aArrowA)
    where a = TyName (Name "a" (Unique 0))
          aArrowA = TyFun () (TyVar () a) (TyVar () a)

-- [ { (builtin ifThenElse) (forall a . a -> a) } (11<=22) ]: evaluation should
-- succeed, typechecking should fail (illegal kind)
iteAtHigherKindWithCond :: Term TyName Name DefaultUni DefaultFun ()
iteAtHigherKindWithCond = Apply () iteAtHigherKind lteExpr

-- [ {(builtin ifThenElse) (forall a . a -> a) } (11<=22) "11 <= 22" "¬(11<=22) ]":
-- illegal kind, but should run
iteAtHigherKindFullyApplied :: Term TyName Name DefaultUni DefaultFun ()
iteAtHigherKindFullyApplied = mkIterApp () (Apply () iteAtHigherKind lteExpr) [stringResultTrue, stringResultFalse]

-- { {(builtin ifThenElse) integer} integer }: should fail to typecheck and also
-- fail during execution (instantiated twice).
iteAtIntegerAtInteger :: Term TyName Name DefaultUni DefaultFun ()
iteAtIntegerAtInteger = TyInst () iteAtInteger integer

-- { [ { (builtin ifThenElse) integer } (11<=22)] integer }: should fail
-- to typecheck and also fail during execution: term expected, type supplied.
iteTypeTermType :: Term TyName Name DefaultUni DefaultFun ()
iteTypeTermType = TyInst () iteAtIntegerWithCond string


-- Various attempts to instantiate the MultiplyInteger builtin

mul ::  Term TyName Name DefaultUni DefaultFun ()
mul = Builtin () MultiplyInteger

-- [ [ (builtin multiplyInteger) 11 ] 22 ]: OK
mulOK :: Term TyName Name DefaultUni DefaultFun ()
mulOK = Apply () (Apply () mul eleven) twentytwo

-- [ [ { (builtin multiplyInteger) string } 11 ] 22 ]: should fail typechecking and also at runtime
mulInstError1 :: Term TyName Name DefaultUni DefaultFun ()
mulInstError1 = Apply () (Apply () (TyInst () mul string) eleven) twentytwo

-- [ [ { (builtin multiplyInteger) 11 ] string } 22 ]: should fail typechecking and also at runtime
mulInstError2 :: Term TyName Name DefaultUni DefaultFun ()
mulInstError2 = Apply () (TyInst () (Apply () mul eleven) string) twentytwo

-- { [ [ (builtin multiplyInteger) 11 ] 22 ] string } : should fail typechecking and also at runtime
mulInstError3 :: Term TyName Name DefaultUni DefaultFun ()
mulInstError3 = TyInst () (Apply () (Apply () mul eleven) twentytwo) string

-- Running the tests

goldenVsPretty :: PrettyPlc a => String -> String -> ExceptT BSL.ByteString IO a -> TestTree
goldenVsPretty extn name value =
    goldenVsString name ("test/Evaluation/Golden/" ++ name ++ extn) $
        either id (BSL.fromStrict . encodeUtf8 . render . prettyPlcClassicDebug) <$> runExceptT value

goldenVsEvaluatedCK :: String -> Term TyName Name DefaultUni DefaultFun () -> TestTree
goldenVsEvaluatedCK name = goldenVsPretty ".plc.golden" name . pure . evaluateCk defBuiltinsRuntime

goldenVsEvaluatedCEK :: String -> Term TyName Name DefaultUni DefaultFun () -> TestTree
goldenVsEvaluatedCEK name = goldenVsPretty ".plc.golden" name . pure . evaluateCek defBuiltinsRuntime

runTypecheck
    :: Term TyName Name DefaultUni DefaultFun ()
    -> Either (Error DefaultUni DefaultFun ()) (Normalized (Type TyName DefaultUni ()))
runTypecheck term =
  runQuoteT $ do
    tcConfig <- getDefTypeCheckConfig ()
    inferType tcConfig term

goldenVsTypechecked :: String -> Term TyName Name DefaultUni DefaultFun () -> TestTree
goldenVsTypechecked name = goldenVsPretty ".type.golden" name . pure . runTypecheck


namesAndTests :: [(String, Term TyName Name DefaultUni DefaultFun ())]
namesAndTests =
   [ ("even2", Apply () even $ metaIntegerToNat 2)
   , ("even3", Apply () even $ metaIntegerToNat 3)
   , ("evenList", Apply () natSum $ Apply () evenList smallNatList)
   , ("polyError", polyError)
   , ("polyErrorInst", TyInst () polyError (mkTyBuiltin @Integer ()))
   , ("closure", closure)
   , ("ite", ite)
   , ("iteUninstantiatedWithCond", iteUninstantiatedWithCond)
   , ("iteUninstantiatedFullyApplied", iteUninstantiatedFullyApplied)
   , ("iteAtInteger", iteAtInteger)
   , ("iteAtIntegerWithCond", iteAtIntegerWithCond)
   , ("iteAtIntegerWrongCondType", iteAtIntegerWrongCondType)
   , ("iteAtIntegerFullyApplied", iteAtIntegerFullyApplied)
   , ("iteAtString", iteAtString)
   , ("iteAtStringWithCond", iteAtStringWithCond)
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
   ]

test_golden :: TestTree
test_golden = testGroup "golden"
              [ testGroup "CK"  $ fmap (uncurry goldenVsEvaluatedCK)  namesAndTests
              , testGroup "CEK" $ fmap (uncurry goldenVsEvaluatedCEK) namesAndTests
              , testGroup "Typechecking" $ fmap (uncurry goldenVsTypechecked) namesAndTests
              ]
