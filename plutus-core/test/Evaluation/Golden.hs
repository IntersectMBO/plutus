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
import           Language.PlutusCore.Evaluation.Machine.ExBudgetingDefaults
import           Language.PlutusCore.Generators.Interesting
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Pretty

import           Control.Monad.Except
import qualified Data.ByteString.Lazy                       as BSL
import           Data.Text.Encoding                         (encodeUtf8)
import           Test.Tasty
import           Test.Tasty.Golden

-- (con integer)
integer :: Type TyName DefaultUni ()
integer = mkTyBuiltin @ Integer ()

-- (con string)
string :: Type TyName DefaultUni ()
string = mkTyBuiltin @ String ()

evenAndOdd :: uni `Includes` Bool => Tuple (Term TyName Name uni) uni ()
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

even :: uni `Includes` Bool => Term TyName Name uni ()
even = runQuote $ tupleTermAt () 0 evenAndOdd

evenAndOddList :: Tuple (Term TyName Name uni) uni ()
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

evenList :: Term TyName Name uni ()
evenList = runQuote $ tupleTermAt () 0 evenAndOddList

smallNatList :: Term TyName Name uni ()
smallNatList = metaListToList nat nats where
    nats = Prelude.map metaIntegerToNat [1,2,3]
    nat = _recursiveType natData

polyError :: Term TyName Name uni ()
polyError = runQuote $ do
    a <- freshTyName "a"
    pure $ TyAbs () a (Type ()) $ Error () (TyVar () a)

-- | For checking that evaluating a term to a non-constant results in all remaining variables
-- being instantiated.
closure :: uni `Includes` Integer => Term TyName Name uni ()
closure = runQuote $ do
    i <- freshName "i"
    j <- freshName "j"
    let integer' = mkTyBuiltin @Integer ()
    pure
        . Apply () (LamAbs () i integer' . LamAbs () j integer' $ Var () i)
        $ mkConstant @Integer () 1

{- Tests for evaluation of builtins, mainly checking that interleaving of term
   and type arguments is correct.  At the moment the only polymorphic builtin
   we have is ifThenElse. -}

-- Various components that we'll use to build larger terms for testing

lte :: Term TyName Name DefaultUni ()
lte = staticBuiltinNameAsTerm LessThanEqInteger

eleven :: Term TyName Name DefaultUni ()
eleven = mkConstant @Integer () 11

twentytwo :: Term TyName Name DefaultUni ()
twentytwo = mkConstant @Integer () 22

stringResultTrue :: Term TyName Name DefaultUni ()
stringResultTrue = mkConstant @String () "11 <= 22"

stringResultFalse :: Term TyName Name DefaultUni ()
stringResultFalse = mkConstant @String () "¬(11 <= 22)"

-- 11 <= 22
lteExpr :: Term TyName Name DefaultUni ()
lteExpr = mkIterApp () lte [eleven, twentytwo]


-- Various combinations of (partial) instantiation/application for ifThenElse

-- (builtin ifThenElse)
ite :: Term TyName Name DefaultUni ()
ite = staticBuiltinNameAsTerm IfThenElse

-- { (builtin ifThenElse) (con integer) }
iteAtInteger :: Term TyName Name DefaultUni ()
iteAtInteger = TyInst () ite integer

-- { (builtin ifThenElse) (con string) }
iteAtString :: Term TyName Name DefaultUni ()
iteAtString = TyInst () ite string

-- { (builtin ifThenElse) (forall a . a -> a) }
-- Evaluation should succeed, but typechecking should fail.
-- You're not allowed to instantiate a builtin at a higher kind.
iteAtHigherKind :: Term TyName Name DefaultUni ()
iteAtHigherKind = TyInst () ite (TyForall () a (Type ()) aArrowA)
    where a = TyName (Name "a" (Unique 0))
          aArrowA = TyFun () (TyVar () a) (TyVar () a)

-- [ (builtin ifThenElse) (11<=22) ]: should fail because ifThenElse isn't instantiated
-- Type expected, term supplied.
iteUninstantiatedOneArg :: Term TyName Name DefaultUni ()
iteUninstantiatedOneArg  = Apply () ite lteExpr

-- [ { (builtin ifThenElse) (con integer) } (11<=22)]: should succeed.
iteAtIntegerOneArg :: Term TyName Name DefaultUni ()
iteAtIntegerOneArg = Apply () iteAtInteger lteExpr

-- [ { (builtin ifThenElse) (con string) } (11<=22) ]: should succeed.
iteAtStringOneArg :: Term TyName Name DefaultUni ()
iteAtStringOneArg = Apply () iteAtString lteExpr

-- [ { (builtin ifThenElse) (forall a . a -> a) } (11<=22) ]: evaluation should
-- succeed, typechecking should fail
iteAtHigherKindOneArg :: Term TyName Name DefaultUni ()
iteAtHigherKindOneArg = Apply () iteAtHigherKind lteExpr

-- (builtin ifThenElse) (11<=22) "11 <= 22" "¬(11<=22)": should succeed.
iteUninstantiatedFullyApplied :: Term TyName Name DefaultUni ()
iteUninstantiatedFullyApplied = mkIterApp () ite [lteExpr, stringResultTrue, stringResultFalse]

-- [ { (builtin ifThenElse)  (con string) } (11<=22) "11 <= 22" "¬(11<=22)" ]: should succeed.
iteAtStringFullyApplied :: Term TyName Name DefaultUni ()
iteAtStringFullyApplied = mkIterApp () iteAtStringOneArg [stringResultTrue, stringResultFalse]

-- [ { (builtin ifThenElse)  (con integer) } (11<=22) "11 <= 22" "¬(11<=22)" ]: should also succeed.
-- However it's ill-typed: at execution time we only check that type
-- instantiations and term arguments are correctly interleaved, not that
-- instantiations are correct.
iteAtIntegerFullyApplied :: Term TyName Name DefaultUni ()
iteAtIntegerFullyApplied = mkIterApp () iteAtIntegerOneArg [stringResultTrue, stringResultFalse]

-- [ {(builtin ifThenElse) (forall a . a -> a) } (11<=22) "11 <= 22" "¬(11<=22) ]":
-- illegal kind, but should succeed.
iteAtHigherKindFullyApplied :: Term TyName Name DefaultUni ()
iteAtHigherKindFullyApplied = mkIterApp () (Apply () iteAtHigherKind lteExpr) [stringResultTrue, stringResultFalse]

-- { {(builtin ifThenElse) integer} integer }: should fail.
iteAtIntegerAtInteger :: Term TyName Name DefaultUni ()
iteAtIntegerAtInteger = TyInst () iteAtInteger integer

-- { [ { (builtin ifThenElse) integer } (11<=22)] integer }: should fail:
-- term expected, type supplied.
iteTypeTermType :: Term TyName Name DefaultUni ()
iteTypeTermType = TyInst () iteAtIntegerOneArg string


-- Various attempts to instantiate the MultiplyInteger builtin

mul ::  Term TyName Name DefaultUni ()
mul = staticBuiltinNameAsTerm MultiplyInteger

-- [ [ (builtin multiplyInteger) 11 ] 22 ]
mulOK :: Term TyName Name DefaultUni ()
mulOK = Apply () (Apply () mul eleven) twentytwo

-- [ [ { (builtin multiplyInteger) string } 11 ] 22 ]
mulInstError1 :: Term TyName Name DefaultUni ()
mulInstError1 = Apply () (Apply () (TyInst () mul string) eleven) twentytwo

-- [ [ { (builtin multiplyInteger) 11 ] string } 22 ]
mulInstError2 :: Term TyName Name DefaultUni ()
mulInstError2 = Apply () (TyInst () (Apply () mul eleven) string) twentytwo

-- { [ [ (builtin multiplyInteger) 11 ] 22 ] string }
mulInstError3 :: Term TyName Name DefaultUni ()
mulInstError3 = TyInst () (Apply () (Apply () mul eleven) twentytwo) string

-- Running the tests

goldenVsPretty :: PrettyPlc a => String -> ExceptT BSL.ByteString IO a -> TestTree
goldenVsPretty name value =
    goldenVsString name ("test/Evaluation/Golden/" ++ name ++ ".plc.golden") $
        either id (BSL.fromStrict . encodeUtf8 . render . prettyPlcClassicDebug) <$> runExceptT value

goldenVsEvaluatedCK :: String -> Term TyName Name DefaultUni () -> TestTree
goldenVsEvaluatedCK name = goldenVsPretty name . pure . evaluateCk mempty

goldenVsEvaluatedCEK :: String -> Term TyName Name DefaultUni () -> TestTree
goldenVsEvaluatedCEK name = goldenVsPretty name . pure . evaluateCek mempty defaultCostModel


namesAndTests :: [(String, Term TyName Name DefaultUni ())]
namesAndTests =
   [ ("even2", Apply () even $ metaIntegerToNat 2)
   , ("even3", Apply () even $ metaIntegerToNat 3)
   , ("evenList", Apply () natSum $ Apply () evenList smallNatList)
   , ("polyError", polyError)
   , ("polyErrorInst", TyInst () polyError (mkTyBuiltin @Integer ()))
   , ("closure", closure)
   , ("ite", ite)
   , ("iteAtInteger", iteAtInteger)
   , ("iteAtString", iteAtString)
   , ("iteAtHigherKind", iteAtHigherKind)
   , ("iteUninstantiatedOneArg", iteUninstantiatedOneArg)
   , ("iteAtIntegerOneArg", iteAtIntegerOneArg)
   , ("iteAtStringOneArg", iteAtStringOneArg)
   , ("iteAtHigherKindOneArg", iteAtHigherKindOneArg)
   , ("iteAtStringFullyApplied", iteAtStringFullyApplied)
   , ("iteUninstantiatedFullyApplied", iteUninstantiatedFullyApplied)
   , ("iteAtIntegerFullyApplied", iteAtIntegerFullyApplied)
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
              ]
